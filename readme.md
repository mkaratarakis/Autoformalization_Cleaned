# Project Overview

This repository contains the data and scripts used for our Lean formalization pipeline experiments. 

## Getting Started

1. **Install dependencies**

   ```bash
   pip install mistralai python-dotenv tqdm pandas pyarrow
   ```
2. **Configure your environment**

   * Create a `.env` file in the project root.
   * Add your `MISTRAL_API_KEY` to this file.
3. **(Optional) Run sampling**

   ```bash
   python3 sampling.py
   ```
4. **Update and build the Lean environment**

   ```bash
   cd "Lean Project"
   lake update
   lake build
   cd ..
   ```
5. **Reproduce experiments**

   ```bash
   cd experiment_XXX
   # Remove previous state if you want a clean run
   rm -f pipeline_state.json mistral_generation_results.csv

   # Run the full pipeline (or specify an ID to test a single theorem)
   python3 pipeline.py [ID]
   ```
6. **Locate generated proofs**

   After the pipeline finishes, you’ll find the proofs in Lean Project/proofs/.

   Make sure they’re inside the Lean environment so you can load and test them.



## Description of the Files

* **Herald\_dataset.parquet**: The full, unprocessed dataset in Parquet format.

* **dataset.csv**: A sampled subset of the full dataset, extracted for efficient processing.

* **sampling.py**: Script to sample 100 entries from the full dataset. Ensures that the total size of header content does not exceed 10000 characters (to keep prompts within reasonable length).

* **Lean Project/**: Local Lean 4 project environment for running `lake` and verifying generated proofs.

* **experiment\_mistral\_baseline/**: Results from a baseline experiment run:

   * **pipeline.py**: Main orchestration script. Reads `dataset.csv`, generates proof attempts via the Mistral model, saves prompts and results, and performs local Lean checks.
   * **system.md**: The system prompt used for the pipeline, defining the assistant’s role and instructions.
   * **prompts/**: Directory containing all generated prompt files. Each file is named `{id}.{attempt}.txt`, where `id` is the theorem identifier and `attempt` is the zero-based attempt number.
   * **proofs/**: Directory storing all generated proof files. Each proof is saved after passing the Lean check or at each failed attempt for debugging.
   * **mistral\_generation\_results.csv**: Boolean success flag for each sample ("yes" or "no").
   * **pipeline\_state.json**: Checkpoint file tracking processed IDs, success count, and total count for resuming interrupted runs.

* **experiment\_mistral\_header\_pipeline/**: Results from another run:
   Same as above.

* **experiment\_mistral\_header\_pipeline\_cut\_state/**: Results from another run:
   Same as above.


