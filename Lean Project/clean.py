import os
import pandas as pd

# File paths
csv_file = "lean_results_real_proofs.csv"
proofs_dir = "real_proofs"

# Load the CSV file
df = pd.read_csv(csv_file)

# Filter rows where Success == "No"
failed_proofs = df[df["Success"] == "No"]["Filename"]

# Delete corresponding .lean files
for filename in failed_proofs:
    file_path = os.path.join(proofs_dir, filename)
    if os.path.exists(file_path):
        os.remove(file_path)
        print(f"Deleted: {file_path}")
    else:
        print(f"File not found: {file_path}")

print("✅ Cleanup complete. All failed proof files have been removed.")
