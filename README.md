## **Files and Directories**

### **Dataset Files**
- **`Herald_dataset.parquet`**  
  - The main dataset containing **formal and informal theorems and proofs**.  
  - Includes fields: `id`, `name`, `formal_theorem`, `informal_theorem`, `formal_proof`, `informal_proof`, `commented_proof`, and `header`.  

- **`filtered_dataset.csv`**  
  - The **cleaned dataset** after filtering out entries where `header == "Unable to analyze"`.  
  - Created by `filter.py`.  

- **`sampled_dataset.csv`**  
  - A **random sample of 300 entries** from `filtered_dataset.csv`.  
  - Created by `sampling.py`.  

### **Dataset Processing Scripts**
- **`filter.py`**  
  - Reads `Herald_dataset.parquet` and **removes entries** where `header == "Unable to analyze"`.  
  - Saves the cleaned data to `filtered_dataset.csv`.  

- **`sampling.py`**  
  - Randomly selects **300** entries from `filtered_dataset.csv`.  
  - Saves the sampled dataset to `sampled_dataset.csv`.  

- **`generate_lean.py`**  
  - Reads `sampled_dataset.csv` and extracts `header` and `formal_proof`.  
  - Modifies `theorem NAME` into `example`, ensuring the resulting Lean file is executable.  
  - Saves each proof as `{id}.lean` inside `Lean Project/real_proofs/`.  

- **`Lean Project/clean.py`**  
  - Reads `lean_results_real_proofs.csv`.  
  - Deletes `.lean` files in `Lean Project/real_proofs/` where `Success == "No"`.  

### **Lean Code and Verification**
- **`Lean Project/real_proofs/`**  
  - Contains **correct Lean proofs** extracted from the dataset and transformed into runnable files.  

- **`Lean Project/first_tries/`**  
  - Contains **initial attempts** at generating Lean proofs using an LLM.  

- **`Lean Project/run_lean_tests.py`**  
  - Runs `lake env lean *.lean` on all files in `real_proofs/` and `first_tries/`.  
  - Records error messages into CSV files.  
  - Outputs a **summary of successful vs. failed proofs**.  

### **LLM Interaction**
- **`spe.ipynb`**  
  - Jupyter notebook for **interacting with the LLM**.  
  - Includes **proof generation and verification experiments**.  
