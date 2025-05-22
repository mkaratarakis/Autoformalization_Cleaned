import os
import re
import subprocess
import pandas as pd

# Determine project root (script is run from root directory)
project_root = os.path.abspath(os.path.dirname(__file__))

# --- Helper functions ---

def extract_import_modules(header: str) -> list[str]:
    """Extract modules from lines like 'import Mathlib.X.Y' or 'import Init.X.Y'."""
    return re.findall(r"import\s+((?:Mathlib|Init)(?:\.\w+)+)", header)


def read_lean_module_code(module: str,
                          mathlib_base: str = None,
                          lean_src_base: str = None,
                          exclude: str = None) -> str:
    """
    Read the source of a Lean module and optionally trim around 'exclude'.
    Uses mathlib_base for Mathlib.* and lean_src_base for Init.* modules.
    """
    # Default base paths inside 'Lean Project'
    if mathlib_base is None:
        mathlib_base = os.path.join(project_root, 'Lean Project', '.lake', 'packages', 'mathlib')
    if lean_src_base is None:
        lean_src_base = os.path.join(project_root, 'Lean Project', 'lean4', 'src')

    rel_path = module.replace('.', os.sep) + '.lean'
    base_dir = mathlib_base if module.startswith('Mathlib.') else lean_src_base
    full_path = os.path.join(base_dir, rel_path)
    if not os.path.exists(full_path):
        return ''

    text = open(full_path, 'r', encoding='utf-8').read()
    if exclude is None:
        return text

    # Trim around the exclude symbol
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
                if ':=' in line and ' by' not in line:
                    colon_mode = True
                elif ':=' in line and ' by' in line:
                    break
        else:
            lines.append(line)
            if ':=' in line:
                break

    # Drop leading imports
    start = 0
    for i, ln in enumerate(lines):
        if ln.strip().startswith('import'):
            start = i + 1
            break
    return ''.join(lines[start:])


def run_lean(file_path: str) -> tuple[str, str, bool]:
    """Run Lean via `lake env lean` in the 'Lean Project' directory and return (stdout, stderr, success)."""
    try:
        # Ensure working directory is 'Lean Project'
        cwd = os.path.join(project_root, 'Lean Project')
        # Use relative path from Lean Project
        rel_file = os.path.relpath(file_path, cwd)
        result = subprocess.run(
            ['lake', 'env', 'lean', rel_file],
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=60
        )
        out = result.stdout.strip()
        err = result.stderr.strip()
        has_err = (
            result.returncode != 0 or
            'error' in out.lower() or
            'error' in err.lower() or
            'unknown identifier' in out.lower() or
            'failed' in out.lower()
        )
        return out, err, not has_err
    except subprocess.TimeoutExpired:
        return '', 'Timeout: Lean took too long to run.', False

# --- Main script ---

def main():
    # 1. Load and filter dataset from project root
    parquet_path = os.path.join(project_root, 'Herald_dataset.parquet')
    df = pd.read_parquet(parquet_path)
    df = df[df['header'] != 'Unable to analyze']

    # 2. Shuffle entries
    df = df.sample(frac=1, random_state=42).reset_index(drop=True)

    selected = []
    seen = set()
    success = 0

    # Prepare output directory and regex
    proofs_dir = os.path.join(project_root, 'Lean Project', 'real_proofs')
    os.makedirs(proofs_dir, exist_ok=True)
    thm_re = re.compile(r'\btheorem\s+\S+')

    for row in df.itertuples(index=False):
        if success >= 1000:
            break
        if row.id in seen:
            continue

        # Build lemma_code
        mods = extract_import_modules(row.header)
        if not mods:
            continue
        excl = row.name.split('.', 1)[1] if '.' in row.name else row.name
        snippets = [read_lean_module_code(m, exclude=excl) for m in mods]
        code = '\n'.join(snippets)
        if not code or len(code) > 10000:
            continue

        # Generate Lean file content at absolute path
        lf = os.path.join(proofs_dir, f'{row.id}.lean')
        if os.path.exists(lf):
            os.remove(lf)
        # Replace 'theorem NAME' with 'example'
        mod_proof = thm_re.sub('example', row.formal_proof, count=1)
        content = f"{row.header}\n\n{mod_proof}"
        with open(lf, 'w', encoding='utf-8') as f:
            f.write(content)

        # Run Lean check using relative path in Lean Project
        out, err, ok = run_lean(lf)
        if ok:
            success += 1
            selected.append(row._asdict())
            seen.add(row.id)
            print(f"[✓] ({success}/1000) id={row.id} accepted")
        else:
            print(f"[✗] ({success}/1000) id={row.id} failed, removing")
            os.remove(lf)

    if success < 1000:
        print(f"Warning: only found {success} valid points.")

    # 6. Save CSV at project root
    out_csv = os.path.join(project_root, 'dataset.csv')
    res_df = pd.DataFrame(selected)
    res_df.sort_values('id', inplace=True)
    res_df.to_csv(out_csv, index=False)
    print(f"Saved {success} records to dataset.csv")

if __name__ == '__main__':
    main()
