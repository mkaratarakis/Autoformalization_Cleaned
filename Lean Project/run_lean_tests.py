import os
import subprocess
import csv

# Define paths
DIRECTORIES = {
    "real_proofs": "lean_results_real_proofs.csv",
}

def run_lean(file_path):
    """Run Lean file and return output, error messages, and success status."""
    try:
        result = subprocess.run(["lake", "env", "lean", file_path], 
                                capture_output=True, text=True, timeout=60)
        output = result.stdout.strip()
        error = result.stderr.strip()

        # Detect errors by checking return code, stderr, and specific error keywords
        has_error = (result.returncode != 0 or 
                     "error" in output.lower() or "error" in error.lower() or
                     "unknown identifier" in output.lower() or "failed" in output.lower())

        return output, error, not has_error  # Return (stdout, stderr, is_success)
    except subprocess.TimeoutExpired:
        return "", "Timeout: Lean took too long to run.", False

def process_directory(directory, output_csv):
    """Run Lean on all .lean files in a directory and save results to a CSV file."""
    if not os.path.exists(directory):
        print(f"Error: Directory {directory} does not exist.")
        return 0, 0

    lean_files = [f for f in os.listdir(directory) if f.endswith(".lean")]
    total_files = len(lean_files)
    successful_runs = 0

    with open(output_csv, mode="w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file)
        writer.writerow(["Filename", "Output", "Error", "Success"])

        for lean_file in lean_files:
            file_path = os.path.join(directory, lean_file)
            output, error, is_success = run_lean(file_path)

            if is_success:
                successful_runs += 1

            print(f"[{'✓' if is_success else '✗'}] {lean_file}")

            writer.writerow([lean_file, output, error, "Yes" if is_success else "No"])

    return successful_runs, total_files

def main():
    total_success = 0
    total_files = 0

    for directory, output_csv in DIRECTORIES.items():
        success, count = process_directory(directory, output_csv)
        total_success += success
        total_files += count

    print(f"\nSummary: {total_success} / {total_files} files ran successfully.")

if __name__ == "__main__":
    main()
