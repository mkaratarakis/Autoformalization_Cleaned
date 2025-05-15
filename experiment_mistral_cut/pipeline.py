import os
import csv
import time
import subprocess
import re
import sys
import json
from mistralai import Mistral
from dotenv import load_dotenv
from tqdm import tqdm

# Load environment variables and initialize API client
load_dotenv()
client = Mistral(api_key=os.getenv("MISTRAL_API_KEY"))

# File and directory constants
INPUT_CSV = "dataset.csv"
OUTPUT_CSV = "mistral_generation_results.csv"
STATE_FILE = "pipeline_state.json"
PROOF_DIR = "Lean Project/real_proofs"
TMP_FILE = "Lean Project/tmp.lean"
PIPELINE_SAVE_DIR = "Lean Project/pipeline"
PROMPTS_DIR = "prompts"
MAX_TRIES = 5


def soft_clear():
	# simulate clearing the visible area
	print("\n" * 10, end="")


def clean_mistral_code(code: str, thm_name: str | None = None) -> str:
	cleaned = re.sub(r"^```lean\s*([\s\S]+?)\s*```$", r"\1", code.strip())
	if thm_name is None:
		return cleaned
	m = re.search(rf"{re.escape(thm_name)}.*", cleaned, flags=re.IGNORECASE)
	if not m:
		return cleaned
	rest = cleaned[m.end():]
	blank = re.search(r"\n\s*\n", rest)
	if blank:
		end_idx = m.end() + blank.start()
		return cleaned[:end_idx]
	return cleaned


def replace_theorem_with_example(proof: str) -> str:
	return re.sub(r"(?m)^\s*theorem\s+\S+", "example", proof, count=1)


def extract_import_modules(header: str) -> list:
	return re.findall(r"import\s+((?:Mathlib|Init)(?:\.\w+)+)", header)


def read_lean_module_code(module: str,
						  mathlib_base="Lean Project/.lake/packages/mathlib",
						  lean_src_base="Lean Project/lean4/src",
						  exclude: str = None) -> str:
	rel_path = module.replace(".", "/") + ".lean"
	if module.startswith("Mathlib."):
		full_path = os.path.join(mathlib_base, rel_path)
	else:
		full_path = os.path.join(lean_src_base, rel_path)
	if not os.path.exists(full_path):
		return f"-- {module} not found. --\n"
	with open(full_path, "r", encoding="utf-8") as f:
		text = f.read()
	if not exclude:
		return f"-- BEGIN {module} --\n" + text + f"\n-- END {module} --\n"
	pattern = re.escape(exclude)
	lines = []
	collecting = False
	colon_mode = False
	for line in text.splitlines(keepends=True):
		if colon_mode:
			lines.append(line)
			break
		if not collecting:
			lines.append(line)
			if re.search(pattern, line):
				collecting = True
				if ":=" in line:
					if " by" in line:
						break
					else:
						colon_mode = True
		else:
			lines.append(line)
			if ":=" in line:
				break
	# drop leading imports
	start_idx = 0
	for ln in lines:
		if ln.strip().startswith("import"):
			break
		start_idx += 1
	snippet = ''.join(lines[start_idx:])
	if snippet and ":= by" in snippet.splitlines()[-1]:
		snippet = re.sub(r":= by.*", ":= by", snippet.strip()) + "\n"
	return snippet


def start_of_proof(header: str, name: str, formal_declaration: str) -> str:
	decl = replace_theorem_with_example(formal_declaration)
	decl = decl.replace("by sorry", "by")
	return f"{header}\n{decl}"


def prompt_for_proof(name: str,
					 informal_theorem: str,
					 formal_theorem: str,
					 informal_proof: str,
					 start: str,
					 header: str) -> str:
	modules = extract_import_modules(header)
	exclude = name.split(".")[-1] if "." in name else name
	full_snippets = [read_lean_module_code(m) for m in modules[:-1]]
	last_snippet = read_lean_module_code(modules[-1], exclude=exclude) if modules else ""
	header_info = "\n".join(full_snippets + [last_snippet])
	formal_theorem = replace_theorem_with_example(formal_theorem)
	return f"""
1. **Informal Theorem**  
{informal_theorem}

2. **Informal Proof**  
{informal_proof}

3. **Formal Theorem**  
{formal_theorem}

4. **Prefix**
{start}

5. **Header Information**  
{header_info}
"""


def prompt_with_error(error_message: str, new_prefix: str) -> str:
	return f"""Below are the error message and proof state for the proof you generated. Please revise the proof accordingly starting with new prefix. DO NOT include backticks, explanations, comments, code fences or any other text before or after the proof.
6. **Error Message and Proof State**
{error_message}

4. **New Prefix**  
   The initial Lean 4 code that you must build on.
{new_prefix}
"""


def save_tmp_file(code: str, path: str = TMP_FILE):
	with open(path, "w", encoding="utf-8") as f:
		f.write(code)


def run_lean_check() -> tuple[bool, str]:
	try:
		res = subprocess.run(
			["lake", "env", "lean", "tmp.lean"],
			cwd="Lean Project",
			capture_output=True,
			text=True,
			timeout=20
		)
		ok = (res.returncode == 0)
		return ok, (res.stdout + res.stderr).strip()
	except Exception as e:
		return False, str(e)


def load_state() -> tuple[set, int, int]:
	if not os.path.exists(STATE_FILE) or os.path.getsize(STATE_FILE) == 0:
		return set(), 0, 0
	try:
		with open(STATE_FILE, "r", encoding="utf-8") as f:
			d = json.load(f)
		return set(d.get("processed_ids", [])), d.get("success_count", 0), d.get("total_count", 0)
	except json.JSONDecodeError:
		return set(), 0, 0


def save_state(processed_ids: set, success_count: int, total_count: int):
	with open(STATE_FILE, "w", encoding="utf-8") as f:
		json.dump({
			"processed_ids": list(processed_ids),
			"success_count": success_count,
			"total_count": total_count
		}, f)


def ensure_dir(path: str):
	os.makedirs(path, exist_ok=True)


def main():
	only_id = sys.argv[1] if len(sys.argv) > 1 else None
	single_mode = only_id is not None
	processed_ids, success_count, total_count = (set(), 0, 0) if single_mode else load_state()

	# prepare directories
	ensure_dir(PIPELINE_SAVE_DIR)
	ensure_dir(PROMPTS_DIR)

	script_dir = os.path.dirname(__file__)
	with open(os.path.join(script_dir, "system.md"), "r", encoding="utf-8") as f:
		system_prompt = f.read()

	with open(INPUT_CSV, "r", encoding="utf-8") as infile:
		rows = list(csv.reader(infile))
	header_row, data_rows = rows[0], rows[1:]

	if not single_mode and not os.path.exists(OUTPUT_CSV):
		with open(OUTPUT_CSV, "w", encoding="utf-8", newline="") as f:
			csv.writer(f).writerow(["id", "success"])

	iterator = tqdm(data_rows, desc="🔄 Processing", ncols=100) if not single_mode else data_rows

	for row in iterator:
		id_ = row[0]
		if only_id and id_ != only_id:
			continue
		if not single_mode and id_ in processed_ids:
			continue

		name = row[1]
		formal_theorem = row[2]
		informal_theorem = row[3]
		formal_proof = row[4]
		informal_proof = row[5]
		header = row[7]

		lean_path = os.path.join(PROOF_DIR, f"{id_}.lean")
		if not os.path.exists(lean_path):
			continue

		total_count += 1
		attempts = []
		error_message = None
		success = False

		thm_name = name.split(".")[-1] if "." in name else name
		start = start_of_proof(header, name, formal_theorem)
		prompt = prompt_for_proof(name, informal_theorem, formal_theorem, informal_proof, start, header)

		convo = [
			{"role": "system", "content": system_prompt},
			{"role": "user", "content": prompt},
			{"role": "assistant", "content": start, "prefix": True}
		]

		for attempt_num in range(1, MAX_TRIES + 1):
			soft_clear()
			print("=" * 80)
			print(f"🔢 Processing ID {id_}, {name} (data point #{total_count})")
			print(f"🔁 Attempt {attempt_num} / {MAX_TRIES} | ✅ Success: {success_count} / Processed: {total_count - 1}")

			# save prompt
			prompt_text = prompt if attempt_num == 1 else prompt_with_error(error_message, start)
			prompt_file = os.path.join(PROMPTS_DIR, f"{id_}-{attempt_num - 1}.txt")
			with open(prompt_file, "w", encoding="utf-8") as pf:
				pf.write(prompt_text)

			try:
				response = client.chat.complete(
					model="mistral-large-latest",
					messages=convo
				)
				raw = response.choices[0].message.content
			except Exception as e:
				raw = f"API ERROR: {e}"

			proof = replace_theorem_with_example(raw)
			# proof = proof.replace("by sorry", "by")
			attempts.append(proof)

			print("\n📜 Generated Lean 4 proof:")
			print(proof)

			save_tmp_file(proof)
			time.sleep(5)

			ok, message = run_lean_check()

			if ok:
				print("✅ Lean check PASSED!")
				success = True
				success_count += 1
				save_tmp_file(
					attempts[-1] + f"\n\n/- ACTUAL PROOF OF {name} -/\n\n" + replace_theorem_with_example(formal_proof),
					os.path.join(PIPELINE_SAVE_DIR, f"{id_}.lean")
				)
				break
			else:
				# save the failed attempt
				save_tmp_file(
					attempts[-1] + f"\n\n/- ACTUAL PROOF OF {name} -/\n\n" +
					replace_theorem_with_example(formal_proof),
					os.path.join(PIPELINE_SAVE_DIR, f"{id_}-{attempt_num}.lean")
				)

				error_message = message

				convo.pop()
				convo.append({"role": "assistant", "content": proof})
 
				m = re.search(r"tmp\.lean:(\d+):\d+:", message)
				err_line = int(m.group(1))
				proof_lines = attempts[-1].splitlines()

				prev_line = proof_lines[err_line-2]
				m = re.match(r'^(\s*)', prev_line)
				indent = m.group(1) if m else ''

				start = "\n".join(proof_lines[:err_line-1])
				proof = f"{start}\n{indent}trace_state\n"

				save_tmp_file(proof)
				time.sleep(5)

				ok, message = run_lean_check()

				if ok:
					print("✅ Lean check PASSED!")
					success = True
					success_count += 1
					save_tmp_file(
						attempts[-1] + f"\n\n/- ACTUAL PROOF OF {name} -/\n\n" + replace_theorem_with_example(formal_proof),
						os.path.join(PIPELINE_SAVE_DIR, f"{id_}.lean")
					)
					break
				else:
					print("❌ Lean check FAILED. Error message:")
					print(message)
					error_message = error_message + "\n" + message

					convo.append({"role": "user", "content": prompt_with_error(error_message, start)})
					convo.append({"role": "assistant", "content": start, "prefix": True})

		if not single_mode:
			with open(OUTPUT_CSV, "a", encoding="utf-8", newline="") as f:
				csv.writer(f).writerow([id_, "yes" if success else "no"])
			processed_ids.add(id_)
			save_state(processed_ids, success_count, total_count)

	print(f"🎯 Final: {success_count} successful out of {total_count} processed.")

if __name__ == "__main__":
	main()
