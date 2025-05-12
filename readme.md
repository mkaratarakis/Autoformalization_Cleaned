# Project Overview

This repository contains the data and scripts used for our Lean formalization pipeline experiments. Below is a description of each file and directory:

* **Herald\_dataset.parquet**: The full, unprocessed dataset in Parquet format.

* **dataset.csv**: A sampled subset of the full dataset, extracted for efficient processing.

* **sampling.py**: Script to sample 100 entries from the full dataset. Ensures that the total size of header content does not exceed 10000 characters (to keep prompts within reasonable length).

* **Lean Project/**: Local Lean 4 project environment for running `lake` and verifying generated proofs.

* **experiment\_header\_contents\_5\_iterations/**: Results from a 5-iteration experiment run:

   * **pipeline.py**: Main orchestration script. Reads `dataset.csv`, generates proof attempts via the Mistral model, saves prompts and results, and performs local Lean checks.
   * **system.md**: The system prompt used for the pipeline, defining the assistant’s role and instructions.
   * **prompts/**: Directory containing all generated prompt files. Each file is named `{id}.{attempt}.txt`, where `id` is the theorem identifier and `attempt` is the zero-based attempt number.
   * **proofs/**: Directory storing all generated proof files. Each proof is saved after passing the Lean check or at each failed attempt for debugging.
   * **mistral\_generation\_results.csv**: Boolean success flag for each sample ("yes" or "no").
   * **pipeline\_state.json**: Checkpoint file tracking processed IDs, success count, and total count for resuming interrupted runs.

* **experiment\_baseline/**: Results from a 5-iteration experiment run:
   Same as above.


## Getting Started

1. Install dependencies:

   ```bash
   pip install mistralai python-dotenv tqdm pandas pyarrow
   ```
2. Ensure your `.env` contains `MISTRAL_API_KEY`.
3. Run sampling (optional):

   ```bash
   python3 sampling.py
   ```
4. Execute main pipeline:

   ```bash
   python3 pipeline.py
   ```
