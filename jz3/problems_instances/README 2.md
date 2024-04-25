# Generated problems / instances and time record
A "problem" refers to the process of generating a full Sudoku solution or a Sudoku puzzle with holes.
An "instance" is when we are checking sat for a particular index when generating the whole sudoku "problem".

## smt2_files
store problems/instances in SMT format

## txt_files
store problems/instances in txt format
`hard_(classic/argyle)_instances.txt` stores particular classic/argyle instance that are hard
`hard_(classic/argyle)_problems.txt` stores whole classic/argyle problems
`(classic/argyle)_time.txt`: time
`mapping.txt`: mapping between txt files with SMT files





**Explaination for file structure of `argyle/classic_time.txt`**: 

Each line of the file is a string version of a dictionary described as follows: 
explaination of the file structure:
```python
time = 5.0
did_time_out = True
tgrid = "1231321093102930129..."
tindex = (1,2)
ttry_Val = 5
tis_sat = "sat"

dict = dict(
"problem":{
    "grid": tgrid, # string
    "index": tindex, # (int, int)
    "try_Val": ttry_Val, # int
    "is_sat": tis_sat # bool
},
constraint1:{ 
# e.g. (True,True,True,True,True)
    "smt_path": "/path/to/smt_file_1.smt",
    "z3": (time, did_time_out "answer sat unsat timeout"),
    "cvc5": (time, did_time_out),
    ...
    "other_solver": (time, did_time_out)
},
constraint2:{
# e.g. (True,False,True,True,True)
    "smt_path": "/path/to/smt_file_1.smt",
    "z3": (time, did_time_out "answer sat unsat timeout"),
    "cvc5": (time, did_time_out),
    ...
    "other_solver": (time, did_time_out)
},
... # other constraints
)
```