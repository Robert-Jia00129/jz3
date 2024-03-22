# Argyle_Sudoku
> This project was partly based on the code from [z3-sudoku](https://github.com/awkwardbunny/z3-sudoku)

This project uses python z3-solver to solve classic sudokus and argyle sudokus using various techniques. It then compares the efficiency of each method and between the sudokus. 

## Directory Structure
- `/analysis`: Includes scripts and notebooks for analyzing solver performance and generating images for reports or presentations.


- `main.py`: This file contains the main function. It takes in a sudoku file and solves it using the methods in sudoku.py. It then prints/ the solution and the time taken to solve it.


- `/problem_instances`: 
  - `/particular_hard_instances_records`: Particular hard **instances** identified during the generation process, in txt and SMT format
  - `/whole_problem_records`: **Whole** sudoku problems in txt and SMT format
  - Details of recording format explained [here](./problems_instances/README.md)


- `/solvers`: Houses executables and related files for various SMT solvers used in the project.


- `/src`: Contains source code for core functionalities. 
  - `Sudoku.py`: Contains all functionalities of building sudoku with various constraints, logging sudoku instances to files in string format and smt format,  `/sudoku_database`: Stores string descriptions of generated Sudoku puzzles, both full (solved) and holes (incomplete).


- `sudoku_database`: Stores the already generated full and holes sudokus
  - `currline.txt`: stores the which line of the full sudokus file should the solver generating sudoku holes start loading from and solving when calling `run_experiment`


- `/tests`: scripts for development testing


- `/time_records`: Direct directory for storing time records from solver runs, highlighting the performance of different solvers.



 The workflow is depicted in the following picture: 

![workflow](./analysis/workflow.jpg)




