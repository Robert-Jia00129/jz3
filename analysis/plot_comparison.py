import ast
import matplotlib.pyplot as plt


class ConstraintPlotter:
    def __init__(self, file_path):
        self.file_path = file_path
        self.parsed_data = self._parse_data()

    def _parse_data(self):
        parsed_data = []
        with open(self.file_path, 'r') as file:
            for line in file:
                try:
                    data_dict = ast.literal_eval(line.strip())
                    parsed_data.append(data_dict)
                except Exception as e:
                    print("Error while parsing the dictionary, but continuing...")
                    continue
        return parsed_data

    def plot_constraints_comparison(self, constraint_comparison_num, solvers=None, x_max=5, y_max=5, combined_plot=False):
        times_constraint_true = {}
        times_constraint_false = {}
        combined_times_true = []
        combined_times_false = []

        for entry in self.parsed_data:
            for constraint, solvers_data in entry.items():
                if type(constraint) == tuple:
                    constraint_value = constraint[constraint_comparison_num]

                    for solver_key, values in solvers_data.items():
                        if solver_key != 'smt_path':
                            time = values[0][0]

                            if solvers is None or solver_key in solvers:
                                if solver_key not in times_constraint_true:
                                    times_constraint_true[solver_key] = []
                                if solver_key not in times_constraint_false:
                                    times_constraint_false[solver_key] = []

                                if constraint_value:
                                    times_constraint_true[solver_key].append(time)
                                    combined_times_true.append(time)
                                else:
                                    times_constraint_false[solver_key].append(time)
                                    combined_times_false.append(time)

        if solvers is None:
            solvers = list(times_constraint_true.keys())

        num_plots = len(solvers) + 1 if combined_plot else len(solvers)
        fig, axs = plt.subplots(num_plots, 1, figsize=(10, 5 * num_plots))

        if num_plots == 1:
            axs = [axs]

        for i, solver_key in enumerate(solvers):
            if solver_key in times_constraint_true and solver_key in times_constraint_false:
                min_length = min(len(times_constraint_true[solver_key]), len(times_constraint_false[solver_key]))
                true_times = times_constraint_true[solver_key][:min_length]
                false_times = times_constraint_false[solver_key][:min_length]

                axs[i].scatter(true_times, false_times, alpha=0.6)
                axs[i].plot([0, x_max], [0, y_max], 'r--')
                axs[i].set_title(f'Time comparison for {solver_key}')
                axs[i].set_xlabel(f'Time when constraint {constraint_comparison_num} is True')
                axs[i].set_ylabel(f'Time when constraint {constraint_comparison_num} is False')
                axs[i].set_xlim([0, x_max])
                axs[i].set_ylim([0, y_max])
                axs[i].grid(True)

        if combined_plot:
            min_length_combined = min(len(combined_times_true), len(combined_times_false))
            combined_true = combined_times_true[:min_length_combined]
            combined_false = combined_times_false[:min_length_combined]

            axs[-1].scatter(combined_true, combined_false, alpha=0.6, color='green')
            axs[-1].plot([0, x_max], [0, y_max], 'r--')
            axs[-1].set_title('Combined Time Comparison for All Solvers')
            axs[-1].set_xlabel(f'Time when constraint {constraint_comparison_num} is True (All Solvers)')
            axs[-1].set_ylabel(f'Time when constraint {constraint_comparison_num} is False (All Solvers)')
            axs[-1].set_xlim([0, x_max])
            axs[-1].set_ylim([0, y_max])
            axs[-1].grid(True)

        plt.tight_layout()
        plt.show()


if __name__ == '__main__':
    time_instances_file_path = '../time-record/particular_hard_instance_time_record/argyle_time.txt'
    plotter = ConstraintPlotter(time_instances_file_path)

    plotter.plot_constraints_comparison(1, solvers=["z3", "cvc5"], x_max=10, y_max=10, combined_plot=True)