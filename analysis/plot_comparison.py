import ast
import matplotlib.pyplot as plt


def plot_constraints_comparison(constraint_comparison_num, solvers=None, file_path=''):
    parsed_data = []

    with open(file_path, 'r') as file:
        for line in file:
            try:
                # Attempt to parse each line as a dictionary
                data_dict = ast.literal_eval(line.strip())
                parsed_data.append(data_dict)
            except Exception as e:
                print("error while parsing the dictionary, but continuing...")
                continue

    # Initializing dictionaries to store time values
    times_constraint_true = {}  # Times when the specified constraint == True
    times_constraint_false = {}  # Times when the specified constraint == False
    combined_times_true = []  # Combined times for all solvers when the constraint is True
    combined_times_false = []  # Combined times for all solvers when the constraint is False

    for entry in parsed_data:
        for constraint, solver in entry.items():
            if type(constraint) == tuple:
                constraint_value = constraint[constraint_comparison_num]
                # print(constraint_value)

                for solver_key, values in solver.items():
                    if solver_key != 'smt_path':  # Exclude the 'smt_path' key
                        time = values[0][0]  # Extract the time value

                        # Check if the current solver matches the specified solver or if all solver are requested
                        # if solvers == "ALL" or solver == solver_key:
                            # Initialize solver lists if not already present
                        if solver_key not in times_constraint_true:
                            times_constraint_true[solver_key] = []
                        if solver_key not in times_constraint_false:
                            times_constraint_false[solver_key] = []

                        # Append the time value to the appropriate list
                        if constraint_value:
                            times_constraint_true[solver_key].append(time)
                            combined_times_true.append(time)
                        else:
                            times_constraint_false[solver_key].append(time)
                            combined_times_false.append(time)

    if solvers is None:
        solvers = list(times_constraint_true.keys())

    num_plots = len(solvers)
    fig, axs = plt.subplots(num_plots, 1, figsize=(10, 5 * num_plots))

    # print(times_constraint_true["z3"])
    if num_plots == 1:  # when there is only one plot
        axs = [axs]

    for i, solver_key in enumerate(solvers):
        if solver_key in times_constraint_true and solver_key in times_constraint_false:
            # Ensure both lists have the same length by truncating the longer one
            min_length = min(len(times_constraint_true[solver_key]), len(times_constraint_false[solver_key]))
            true_times = times_constraint_true[solver_key][:min_length]
            false_times = times_constraint_false[solver_key][:min_length]

            axs[i].scatter(true_times, false_times, alpha=0.6)
            axs[i].plot([0, 5], [0, 5], 'r--')
            axs[i].set_title(f'Time comparison for {solver_key}')
            axs[i].set_xlabel(f'Time when constraint {constraint_comparison_num} is True')
            axs[i].set_ylabel(f'Time when constraint {constraint_comparison_num} is False')
            axs[i].set_xlim([0, 5])
            axs[i].set_ylim([0, 5])
            axs[i].grid(True)
    # # Plotting the data
    # num_plots = len(times_constraint_true) + 1 if solvers == "ALL" else 1
    # fig, axs = plt.subplots(num_plots, 1, figsize=(10, 5 * num_plots))
    #
    # if num_plots == 1:  # when there is only one plot
    #     axs = [axs]
    #
    # for i, solver_key in enumerate(solvers):
    #     if solver_key in times_constraint_true and solver_key in times_constraint_false:
    #         # Ensure both lists have the same length by truncating the longer one
    #         min_length = min(len(times_constraint_true[solver_key]), len(times_constraint_false[solver_key]))
    #         true_times = times_constraint_true[solver_key][:min_length]
    #         false_times = times_constraint_false[solver_key][:min_length]
    #
    #         axs[i].scatter(true_times, false_times, alpha=0.6)
    #         axs[i].plot([0, 5], [0, 5], 'r--')
    #         axs[i].set_title(f'Time comparison for {solver_key}')
    #         axs[i].set_xlabel(f'Time when constraint {constraint_comparison_num} is True')
    #         axs[i].set_ylabel(f'Time when constraint {constraint_comparison_num} is False')
    #         axs[i].set_xlim([0, 5])
    #         axs[i].set_ylim([0, 5])
    #         axs[i].grid(True)
    #
    # # time instances for individual solver (if specified)
    # for i, solver_key in enumerate(times_constraint_true.keys()):
    #     # Ensure both lists have the same length by truncating the longer one
    #     min_length = min(len(times_constraint_true[solver_key]), len(times_constraint_false[solver_key]))
    #     true_times = times_constraint_true[solver_key][:min_length]
    #     false_times = times_constraint_false[solver_key][:min_length]
    #
    #     axs[i].scatter(true_times, false_times, alpha=0.6)
    #     axs[i].plot([0, 5], [0, 5], 'r--')
    #     axs[i].set_title(f'Time comparison for {solver_key}')
    #     axs[i].set_xlabel(f'Time when constraint {constraint_comparison_num} is True')
    #     axs[i].set_ylabel(f'Time when constraint {constraint_comparison_num} is False')
    #     axs[i].set_xlim([0, 5])
    #     axs[i].set_ylim([0, 5])
    #     axs[i].grid(True)

    # Combined plot for ALL solvers
    # if solvers == "ALL":
    #     min_length_combined = min(len(combined_times_true), len(combined_times_false))
    #     combined_true = combined_times_true[:min_length_combined]
    #     combined_false = combined_times_false[:min_length_combined]
    #
    #     axs[-1].scatter(combined_true, combined_false, alpha=0.6, color='green')
    #     axs[-1].plot([0, 5], [0, 5], 'r--')
    #     axs[-1].set_title('Combined Time Comparison for All Solvers')
    #     axs[-1].set_xlabel(f'Time when constraint {constraint_comparison_num} is True (All Solvers)')
    #     axs[-1].set_ylabel(f'Time when constraint {constraint_comparison_num} is False (All Solvers)')
    #     axs[-1].set_xlim([0, 5])
    #     axs[-1].set_ylim([0, 5])
    #     axs[-1].grid(True)

    plt.tight_layout()
    plt.show()


if __name__ == '__main__':
    time_instances_file_path = '../time-record/particular_hard_instance_time_record/argyle_time.txt'
    # plot_constraints_comparison(1,
    #                             file_path=time_instances_file_path)  # Compare between distinct and pbeq for all solvers
    plot_constraints_comparison(1, solvers=["z3","cvc5"],
                                file_path=time_instances_file_path)  # compare between distinct and pbeq, but specifically for z3
