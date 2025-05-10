import os
import re
import pandas as pd

# File paths
input_file = "dataset.csv"
output_dir = "Lean Project/real_proofs"

# Create output directory if it doesn't exist
os.makedirs(output_dir, exist_ok=True)

# Load the sampled dataset
df = pd.read_csv(input_file)

# Regular expression to match "theorem NAME" and replace it with "example"
theorem_pattern = re.compile(r'\btheorem\s+\S+', re.MULTILINE)

# Process each row and create a Lean file
for _, row in df.iterrows():
    file_name = f"{row['id']}.lean"
    file_path = os.path.join(output_dir, file_name)

    # Extract header and formal proof
    header = row['header']
    formal_proof = row['formal_proof']

    # Replace "theorem NAME" with "example"
    modified_proof = theorem_pattern.sub("example", formal_proof, count=1)

    # Combine header and modified formal proof
    lean_content = f"{header}\n\n{modified_proof}"

    # Write to a Lean file
    with open(file_path, "w", encoding="utf-8") as f:
        f.write(lean_content)

    print(f"Saved: {file_path}")

print("✅ All Lean files have been created in Lean Project/real_proofs/")
