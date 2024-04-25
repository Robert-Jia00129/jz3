# time_analysis.py
import os
import matplotlib.pyplot as plt

def read_time_from_line(file_path, line_num):
    """Read a specific line from a file and return the time value and timeout status."""
    with open(file_path, 'r') as file:
        for i, line in enumerate(file):
            if i == line_num:
                time_taken, timeout_status = line.strip().split(',')
                return float(time_taken), timeout_status == '1'
    return None, False


def escape_latex(s):
    """Escapes LaTeX special characters in a given string."""
    return s.replace('#', '\\#').replace('%', '\\%').replace('&', '\\&')


def generate_latex(only_constraint_false_timeout_count, both_constraint_timeout_count,
                   both_no_timeout_count, only_constraint_true_timeout_count,
                   constraint_true, constraint_false):
    # Escape special LaTeX characters in constraint names
    constraint_true = constraint_true.replace('_', '\\_')
    constraint_false = constraint_false.replace('_', '\\_')

    # calculate percentage:
    total_count = only_constraint_false_timeout_count + both_constraint_timeout_count + \
                  both_no_timeout_count + only_constraint_true_timeout_count

    # Format numbers as percentages with two decimal places and include the raw count
    only_constraint_false_timeout = f"{only_constraint_false_timeout_count} ({only_constraint_false_timeout_count / total_count * 100:.2f}\\%)"
    both_constraint_timeout = f"{both_constraint_timeout_count} ({both_constraint_timeout_count / total_count * 100:.2f}\\%)"
    both_no_timeout = f"{both_no_timeout_count} ({both_no_timeout_count / total_count * 100:.2f}\\%)"
    only_constraint_true_timeout = f"{only_constraint_true_timeout_count} ({only_constraint_true_timeout_count / total_count * 100:.2f}\\%)"

    # # Format numbers as percentages with two decimal places
    # only_constraint_false_timeout = f"{only_constraint_false_timeout * 100:.2f}\\%"
    # both_constraint_timeout = f"{both_constraint_timeout * 100:.2f}\\%"
    # both_no_timeout = f"{both_no_timeout * 100:.2f}\\%"
    # only_constraint_true_timeout = f"{only_constraint_true_timeout * 100:.2f}\\%"

    latex_code: str = f"""
\\begin{{table}}[ht]
\\centering
\\begin{{tabular}}{{|m{{1.5cm}}|c|c|c|}}
\\cline{{3-4}}
\\multicolumn{{2}}{{c|}}{{}} & \\multicolumn{{2}}{{c|}}{{{constraint_true}}} \\\\ \\cline{{3-4}} 
\\multicolumn{{2}}{{c|}}{{}} & No Timeout & Timeout \\\\ \\hline
\\multirow{{2}}{{*}}{{{constraint_false}}} & Timeout & {only_constraint_false_timeout} & {both_constraint_timeout} \\\\ \\cline{{2-4}} 
 & No Timeout & {both_no_timeout} & {only_constraint_true_timeout} \\\\ \\hline
\\end{{tabular}}
\\caption{{Comparison of timeout occurrences {constraint_true} and {constraint_false}}}
\\end{{table}}
"""
    return latex_code


def plot_comparison_for_constraint(files_directory, constraint_true='distinct', constraint_false='PbEq',
                                   time_cap=5,save_as_file:str=""):
    all_files = os.listdir(files_directory)
    times_full_true = []
    times_full_false = []
    times_holes_true = []
    times_holes_false = []
    timeout_only_false = 0
    timeout_both = 0
    never_timed_out = 0
    timeout_only_true = 0

    for file_name in all_files:
        if constraint_true in file_name:
            constraint_false_file = file_name.replace(constraint_true, constraint_false)
            constraint_false_file_path = os.path.join(files_directory, constraint_false_file)
            if not os.path.isfile(constraint_false_file_path):
                continue
            constraint_true_file_path = os.path.join(files_directory, file_name)
            time_type = 'full' if 'full_time' in file_name else 'holes'

            with open(constraint_true_file_path, 'r') as true_file, open(constraint_false_file_path, 'r') as false_file:
                for i, (true_line, false_line) in enumerate(zip(true_file, false_file)):
                    true_time, true_timeout = read_time_from_line(constraint_true_file_path, i)
                    false_time, false_timeout = read_time_from_line(constraint_false_file_path, i)

                    # classify all points that take more than time_cap as timeout
                    true_timeout = true_time > time_cap
                    false_timeout = false_time > time_cap

                    true_time = min(true_time, time_cap)
                    false_time = min(false_time, time_cap)
                    # Update timeout table
                    if true_timeout and not false_timeout:
                        timeout_only_true += 1
                    elif not true_timeout and false_timeout:
                        timeout_only_false += 1
                    elif true_timeout and false_timeout:
                        timeout_both += 1
                    else:
                        never_timed_out += 1

                    # Plot instances
                    if time_type == 'full':
                        times_full_true.append(true_time)
                        times_full_false.append(false_time)
                    else:
                        times_holes_true.append(true_time)
                        times_holes_false.append(false_time)

    # Plotting
    plt.figure(figsize=(6, 6))
    plt.scatter(times_full_true, times_full_false, color='green', alpha=0.5, label='Full Time')
    plt.scatter(times_holes_true, times_holes_false, color='blue', alpha=0.5, label='Holes Time')
    plt.plot([0, time_cap], [0, time_cap], 'r--')
    plt.xlim(0, time_cap)
    plt.ylim(0, time_cap)
    plt.xlabel(f'Times for {constraint_true} capped at {time_cap} seconds')
    plt.ylabel(f'Times for {constraint_false} capped at {time_cap} seconds')
    plt.title(f'Comparison of Times: {constraint_true} vs. {constraint_false} within [0, {time_cap}] seconds')
    plt.legend()
    plt.grid(True)
    if save_as_file:
        plt.savefig(save_as_file)
    plt.show()
    timeout_count_lst = [timeout_only_false, timeout_both, never_timed_out, timeout_only_true]

    print(generate_latex(*timeout_count_lst, constraint_true, constraint_false))
    return timeout_only_true, timeout_both, timeout_only_false, timeout_both


if __name__ == '__main__':
    TIME_OUT = 5

    files_directory = '/Users/jiazhenghao/Desktop/CodingProjects/jz3/jz3/time-record/whole_problem_time_records'
    # plot_comparison_for_constraint(files_directory, 'distinct', 'PbEq', time_cap=200)  # extended
    plot_name = "full_problem_no_num comparison"
    # plot_comparison_for_constraint(files_directory, 'is_num', 'is_bool',
    #                                time_cap=5,)
    constraint_true_false_lst = [
        ("classic","argyle"),
        ("distinct","PbEq"),
        ("percol","inorder"),
        ("is_bool","is_num"),
        ("prefill","no_prefill")
    ]
    # for (true_constraint,false_constraint) in constraint_true_false_lst:
    #     plot_comparison_for_constraint(files_directory, true_constraint,false_constraint,
    #                                    save_as_file='./images/whole_distinct_5s_cap', time_cap=5)

    plot_comparison_for_constraint(files_directory,"distinct","PbEq",save_as_file='./images/whole_distinct_5s_cap',time_cap=5)
    # forgot to handle timeout