# JZ3
> This project was partly based on the code from [z3-sudoku](https://github.com/awkwardbunny/z3-sudoku)

## QuickStart
After installation, let's look at the example in [quickstart](./jz3/quickstart.py)

Given a problem: we want to see if we can assign variable x an integer value between 8 and 17, but not 12. There are two ways of encoding it (different approaches to solving the problem): encoding1, encoding2. These encode excactly the same problem.  

We represent these 2 encodings as condition1, condition2 (each condition itself is a variable!). Now we want to solve the problem with either approach. `solver.add_global_constraints(z3.Or(condition1, condition2))`

But we might not want to use both approaches at the same time, so we have `solver.add_global_constraints(z3.Distinct(condition1, condition2))`


## Resources & Links
This project uses python z3-solver to benchmark encoding techniques to solving the same problem. 
It then compares the efficiency of each method and between different encoding techniques.

The link to the PyPi package is [https://pypi.org/project/jz3/](https://pypi.org/project/jz3/)
The link to the github repo is [https://github.com/Robert-Jia00129/jz3](https://github.com/Robert-Jia00129/jz3)

- `solvers` module: Houses executables and related files for various SMT solvers used in the project.
- `analysis` module: After running experiments. Analyze and compare which assignment of conditional variables

