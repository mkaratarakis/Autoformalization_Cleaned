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

# Load API key
load_dotenv()
client = Mistral(api_key=os.getenv("MISTRAL_API_KEY"))

INPUT_CSV = "dataset.csv"
OUTPUT_CSV = "mistral_generation_results.csv"
STATE_FILE = "pipeline_state.json"
PROOF_DIR = "Lean Project/real_proofs"
TMP_FILE = "Lean Project/tmp.lean"
PIPELINE_SAVE_DIR = "Lean Project/pipeline"
MAX_TRIES = 5


def soft_clear():
	# simulate Command+L: push previous output off the visible area but keep scrollback
	print("\n" * 10, end="")

# Clean Mistral output
def clean_mistral_code(code: str, thm_name: str | None = None) -> str:
	"""
	Strip ```lean fences and return the text from the beginning up to the
	first blank line *after* the line containing ``theorem {thm_name}``.
	If `thm_name` is None or the marker isn't found, the cleaned string is
	returned unchanged.
	"""
	# 1 strip ```lean … ``` wrapper (if any)
	cleaned = re.sub(r"^```lean\s*([\s\S]+?)\s*```$", r"\1", code.strip())

	if thm_name is None:
		return cleaned  # nothing to look for

	# 2 locate the specific theorem line
	m = re.search(rf"{re.escape(thm_name)}.*", cleaned,
	              flags=re.IGNORECASE)
	if not m:
		return cleaned  # marker absent → return whole string

	# 3 find the first empty line after it
	rest = cleaned[m.end():]
	blank = re.search(r"\n\s*\n", rest)
	if blank:
		end_idx = m.end() + blank.start()
		return cleaned[:end_idx]

	return cleaned  # no blank line found

# Replace `theorem name` with `example`
def replace_theorem_with_example(proof: str) -> str:
	return re.sub(r"(?m)^\s*theorem\s+\S+", "example", proof, count=1)

def extract_import_modules(header: str) -> list:
	"""Extract module names from 'import Mathlib.X.Y' lines."""
	return re.findall(r"import\s+((?:Mathlib|Init)(?:\.\w+)+)", header)
# Updated read_lean_module_code with distinct paths for Mathlib vs core Init modules, and trimmed exclude logic

def read_lean_module_code(module: str,
                          mathlib_base="Lean Project/.lake/packages/mathlib",
                          lean_src_base="Lean Project/lean4/src",
                          exclude: str = None) -> str:
    """
    Convert a Lean module name to its file path, read its content, and optionally trim
    up to the `exclude` marker. Uses mathlib_base for Mathlib.* modules and lean_src_base
    for core Init.* modules.
    """
    import os, re

    # Build relative path and select base directory
    rel_path = module.replace(".", "/") + ".lean"
    if module.startswith("Mathlib."):
        full_path = os.path.join(mathlib_base, rel_path)
    else:
        full_path = os.path.join(lean_src_base, rel_path)

    if not os.path.exists(full_path):
        print(f"Warning: {full_path} not found.")
        return f"-- {module} not found. --\n"

    with open(full_path, "r", encoding="utf-8") as f:
        module_text = f.read()

    # If no exclude marker is provided, return entire module wrapped in comments
    if not exclude:
        return f"-- BEGIN {module} --\n" + module_text + f"\n-- END {module} --\n"

    # Otherwise, trim lines around the exclude marker
    pattern = re.escape(exclude)
    trimmed_lines = []
    collecting = False
    colon_mode = False
    for line in module_text.splitlines(keepends=True):
        if colon_mode:
            trimmed_lines.append(line)
            break
        if not collecting:
            trimmed_lines.append(line)
            if re.search(pattern, line):
                collecting = True
                if ":=" in line:
                    if " by" in line:
                        break
                    else:
                        colon_mode = True
        else:
            trimmed_lines.append(line)
            if ":=" in line:
                break

    # Remove leading import statements
    start_idx = 0
    for ln in trimmed_lines:
        if ln.strip().startswith("import"):
            break
        start_idx += 1
    trimmed_lines = trimmed_lines[start_idx:]

    # Simplify any trailing ':= by ...' to just ':= by'
    if trimmed_lines and ":= by" in trimmed_lines[-1]:
        trimmed_lines[-1] = re.sub(r":= by.*", ":= by", trimmed_lines[-1].strip()) + "\n"

    return ''.join(trimmed_lines)


# Updated start_of_proof to distinguish Mathlib vs core Init modules and rename non-Mathlib declarations
def start_of_proof(header: str,
                   name: str,
                   formal_declaration: str) -> str:
    """
    Prepare the beginning of the Lean proof file:
    1. Include all but the last import modules fully from the header.
    2. If the last import is from Mathlib, include its declarations up to the theorem.
    3. Otherwise (e.g., core Init.*), include only the import lines and an anonymous example declaration without name or a trailing 'sorry'.
    """
    import re
    modules = extract_import_modules(header)
    if not modules:
        return header

    # Gather imports except the last one
    import_lines = [f"import {mod}" for mod in modules[:-1]]

    last_mod = modules[-1]
    exclude = name.split(".", 1)[1] if "." in name else name

    if last_mod.startswith("Mathlib."):
        # Include trimmed Mathlib module snippet
        clipped = read_lean_module_code(last_mod, exclude=exclude)
        return "\n".join(import_lines + [clipped])

    # Core module: skip loading its code to avoid duplicate definitions
    # Rename the declaration to an anonymous 'example' to avoid clashes and drop the original name
    # Lean syntax: 'example (args) : Prop :='
    # Replace leading 'def <...>' or 'theorem <...>' plus module qualifiers up to '(' with 'example '
    renamed_decl = re.sub(r'^(?:def|theorem)\s+[^\(]+', 'example ', formal_declaration)
    # Remove any trailing 'sorry'
    renamed_decl = re.sub(r'\s*sorry\s*$', '', renamed_decl).rstrip()

    return "\n".join(import_lines + [renamed_decl])

def replace_proofs_with_sorry_in_text(text: str) -> str:
	lines = text.splitlines(keepends=True)
	new_lines = []
	in_proof = False
	for line in lines:
		if not in_proof and ":=" in line:
			prefix, _ = line.split(":=", 1)
			new_lines.append(prefix.strip() + " := by sorry\n")
			in_proof = True
		elif in_proof:
			if line.strip() == "":
				new_lines.append(line)
				in_proof = False
			# Skip lines within the proof block
		else:
			new_lines.append(line)
	return "".join(new_lines)

def prompt_for_proof(name, informal_theorem, formal_theorem, informal_proof, header, start):
	# Step 1: extract all import modules from the header
	modules = extract_import_modules(header)
	# Step 2: read the contents of these modules
	lemma_code = "\n".join([read_lean_module_code(m) for m in modules[:-1]])

	# Step 3: build the prompt string
	return f"""Formalize the provided proof of the following theorem in Lean 4. 
Write only Lean 4 code, and do not include explanations, comments, code tags, or other artefacts. 
Do not use Lean 3 syntax. 
DO NOT write down proofs of any other theorems. 
Use ONLY definitions and lemmas from the allowed imports.
DO NOT write anything else before or after the proof. 

<informal_statement> {informal_theorem} </informal_statement>
<informal_proof> {informal_proof} </informal_proof>

The following are contents of definitions and lemmas from the imports in the header. You may find them useful:
<provided_lemmas>
{lemma_code}
</provided_lemmas>

I’ve provided the formalization’s opening for you. Please continue from there to complete the proof.
<starting_code>
{start}
</starting_code>
"""

def prompt_with_error(informal_theorem, formal_theorem, informal_proof, previous_proof, error_message, header):
	return f"""The previous Lean 4 proof attempt contains errors. Please revise it by referring closely to the original informal proof and using the following Lean feedback for corrections.

<error_message> {error_message} </error_message>

You must refer to the original informal proof above along with the Lean error message to revise the proof. 
Return only corrected Lean 4 code, and do not include explanations."""

# Save proof to temporary file
def save_tmp_file(code, path=TMP_FILE):
	with open(path, "w", encoding="utf-8") as f:
		f.write(code)

# Run Lean check
def run_lean_check():
	try:
		result = subprocess.run(
			["lake", "env", "lean", "tmp.lean"],
			cwd="Lean Project",
			capture_output=True,
			text=True,
			timeout=20
		)
		success = result.returncode == 0
		return success, (result.stdout + result.stderr).strip()
	except subprocess.TimeoutExpired:
		return False, "Timeout during Lean check"
	except Exception as e:
		return False, f"Subprocess error: {str(e)}"

# Load/Save state functions are defined below
		f.write(id + "\n")


# ---- load_state ----
def load_state():
    if not os.path.exists(STATE_FILE) or os.path.getsize(STATE_FILE) == 0:
        return set(), 0, 0
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return (set(data.get("processed_ids", [])),
                data.get("success_count", 0),
                data.get("total_count", 0))
    except json.JSONDecodeError:
        return set(), 0, 0

def save_state(processed_ids, success_count, total_count):
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump({
            "processed_ids": list(processed_ids),
            "success_count": success_count,
            "total_count": total_count
        }, f)


def ensure_pipeline_dir():
	os.makedirs(PIPELINE_SAVE_DIR, exist_ok=True)

def main():
	only_id = sys.argv[1] if len(sys.argv) > 1 else None
	single_mode = only_id is not None
	processed_ids, success_count, total_count = (set(), 0, 0) if single_mode else load_state()

	with open(INPUT_CSV, mode="r", encoding="utf-8") as infile:
		csv_reader = list(csv.reader(infile))
		header_row = csv_reader[0]
		data_rows = csv_reader[1:]

	if not single_mode:
		if not os.path.exists(OUTPUT_CSV):
			with open(OUTPUT_CSV, "w", encoding="utf-8", newline="") as f:
				csv.writer(f).writerow(["id", "success"])
		ensure_pipeline_dir()
	ensure_pipeline_dir()

	iterator = tqdm(data_rows, desc="🔄 Processing", ncols=100) if not single_mode else data_rows

	for row in iterator:
		id = row[0]
		if only_id and id != only_id:
			continue
		if not only_id and id in processed_ids:
			continue

		name = row[1]
		informal_theorem = row[3]
		formal_theorem = row[2]
		informal_proof = row[5]
		formal_proof = row[4]
		header = row[7]

		lean_path = os.path.join(PROOF_DIR, f"{id}.lean")
		if not os.path.exists(lean_path):
			continue

		total_count += 1
		attempts = []
		error_message = None
		success = False

		start = start_of_proof(header, name, formal_theorem)
		#thm_name = name.split(".")[-1]
		thm_name = name.split(".", 1)[1] if "." in name else name

		prompt = prompt_for_proof(name, informal_theorem, formal_theorem, informal_proof, header, start)
	
		print(prompt)
		# print(start)
		convo = [{"role": "user", "content": prompt}, {"role": "assistant","content":start,"prefix": True}]

		for attempt_num in range(1, MAX_TRIES + 1):
			soft_clear()
			print("="*80)
			print(f"🔢 Processing ID {id}, {name} (data point #{total_count})")
			print(f"🔁 Attempt {attempt_num} / {MAX_TRIES} | ✅ Success: {success_count} / Processed: {total_count - 1}")

			try:
				response = client.chat.complete(
					model="mistral-large-latest",
					messages=convo
				)
				raw = response.choices[0].message.content

				proof = clean_mistral_code(raw, thm_name)
				#proof = replace_theorem_with_example(proof)

				attempts.append(proof)
			except Exception as e:
				print("❌ API ERROR:", e)
				attempts.append(f"API ERROR: {e}")
				convo.pop()
				convo.append({"role": "assistant", "content": raw})
				convo.append({"role": "user", "content": prompt_with_error(informal_theorem, formal_theorem, informal_proof, attempts[-1], error_message, header)})
				convo.append({"role": "assistant", "content": start, "prefix": True})
				break

			print("\n📜 Generated Lean 4 proof:")
			print(proof)

			save_tmp_file(proof)
			time.sleep(5)

			ok, message = run_lean_check()

			if ok:
				print("✅ Lean check PASSED!")
				success = True
				success_count += 1
				save_tmp_file(attempts[-1] + f"\n\n/- ACTUAL PROOF OF {name} -/\n\n" + replace_theorem_with_example(formal_proof), os.path.join(PIPELINE_SAVE_DIR, f"{id}.lean"))
				break
			else:
				print("❌ Lean check FAILED. Error message:")
				print(message)
				error_message = message
				save_tmp_file(attempts[-1] + f"\n\n/- ACTUAL PROOF OF {name} -/\n\n" + replace_theorem_with_example(formal_proof), os.path.join(PIPELINE_SAVE_DIR, f"{id}-{attempt_num}.lean"))
				convo.pop()
				convo.append({"role": "assistant", "content": raw})
				convo.append({"role": "user", "content": prompt_with_error(informal_theorem, formal_theorem, informal_proof, attempts[-1], error_message, header)})
				convo.append({"role": "assistant", "content": start, "prefix": True})

		if not single_mode:
			with open(OUTPUT_CSV, "a", encoding="utf-8", newline="") as f:
							csv.writer(f).writerow([id, "yes" if success else "no"])
			processed_ids.add(id)
			save_state(processed_ids, success_count, total_count)
			save_state(processed_ids, success_count, total_count)

	print(f"🎯 Final: {success_count} successful out of {total_count} processed.")

if __name__ == "__main__":
	main()
