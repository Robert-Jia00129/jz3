import difflib


def display_file_diff(file1_path, file2_path, output_file):
    with open(file1_path, 'r') as file1, open(file2_path, 'r') as file2:
        file1_lines = file1.readlines()
        file2_lines = file2.readlines()

    differ = difflib.Differ()
    diff_lines = list(differ.compare(file1_lines, file2_lines))

    with open(output_file, 'w') as outfile:
        outfile.write("Difference between the two files:\n")
        outfile.write("Left: Custom SMT2 file | Right: Z3 SMT2 output\n")
        outfile.write("----------------------------------------------------\n")

        for line in diff_lines:
            if line.startswith('  '):
                outfile.write(line)
            elif line.startswith('- '):
                outfile.write(f"[-] {line[2:]}")
            elif line.startswith('+ '):
                outfile.write(f"[+] {line[2:]}")

    print(f"Diff output written to {output_file}")


# Usage example
file1_path = "my-smt.smt2"
file2_path = "z3_sudoku_solved.smt2"
output_file = "diff.txt"
display_file_diff(file1_path, file2_path, output_file)
