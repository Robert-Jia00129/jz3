import ast
import matplotlib.pyplot as plt
import numpy as np


class ConstraintPlotter:
    def __init__(self, file_path):
        self.file_path = file_path
        self.parsed_data = self._parse_data()
        self.x_max = 5
        self.y_max = 5
        self.width = 10
        self.height = 5
        self.opacity = 0.6
        self.marker_size=None
        self.line_style = 'r--'
        self.grid = True

    def set_graph_properties(self, x_max=5, y_max=5, width=10, height=5, opacity=0.6, marker_size=None,
                             line_style='r--', grid=True):
        self.x_max = x_max
        self.y_max = y_max
        self.width = width
        self.height = height
        self.opacity = opacity
        self.marker_size = marker_size
        self.line_style = line_style
        self.grid = grid

    def _parse_data(self):
        parsed_data = []
        with open(self.file_path, 'r') as file:
            for line in file:
                try:
                    data_dict = ast.literal_eval(line.strip())
                    parsed_data.append(data_dict)
                except Exception as e:
                    print("Error while parsing the dictionary, but continuing...")
                    print(f"The line that incurred the issue is: ---->\n{e}\n<----- If nothing is printed in between, it's an empty space or new line encountered")
                    continue
        return parsed_data

    def plot_constraints_comparison(self, constraint_comparison_num, solvers=None, combined_plot=False, constraint_names=None):
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
        fig, axs = plt.subplots(num_plots, 1, figsize=(self.width, self.height * num_plots))

        if num_plots == 1:
            axs = [axs]

        for i, solver_key in enumerate(solvers):
            if solver_key in times_constraint_true and solver_key in times_constraint_false:
                min_length = min(len(times_constraint_true[solver_key]), len(times_constraint_false[solver_key]))
                true_times = times_constraint_true[solver_key][:min_length]
                false_times = times_constraint_false[solver_key][:min_length]
                # adjusting the datapoints to be within or at the edge of the graph
                true_times = np.clip(true_times, 0, self.x_max)
                false_times = np.clip(false_times, 0, self.y_max)
                for ele in false_times:
                    if ele >= self.y_max:
                        raise "AS"

                axs[i].scatter(true_times, false_times, alpha=self.opacity,s=self.marker_size)
                axs[i].plot([0, self.x_max], [0, self.y_max], self.line_style)
                axs[i].set_title(f'Time comparison for {solver_key}')

                # set x y label according to constraint name
                if constraint_names and len(constraint_names) > constraint_comparison_num:
                    constraint_name_true, constraint_name_false = constraint_names[constraint_comparison_num]
                    axs[i].set_xlabel(f'Time when {constraint_name_true}')
                    axs[i].set_ylabel(f'Time when {constraint_name_false}')
                else:
                    axs[i].set_xlabel(f'Time when constraint {constraint_comparison_num} is True')
                    axs[i].set_ylabel(f'Time when constraint {constraint_comparison_num} is False')

                axs[i].set_xlim([0, self.x_max])
                axs[i].set_ylim([0, self.y_max])
                axs[i].grid(self.grid)

        if combined_plot:
            min_length_combined = min(len(combined_times_true), len(combined_times_false))
            # assert len(combined_times_false)==len(combined_times_true), f"There are unequal cases of conditions {len(combined_times_true)}, {len(combined_times_false)}"
            combined_true = combined_times_true[:min_length_combined]
            combined_false = combined_times_false[:min_length_combined]

            axs[-1].scatter(combined_true, combined_false, alpha=self.opacity,s=self.marker_size, color='green')
            axs[-1].plot([0, self.x_max], [0, self.y_max], 'r--')
            axs[-1].set_title('Combined Time Comparison for All Solvers')

            # set x y label according to constraint name
            if constraint_names and len(constraint_names) > constraint_comparison_num:
                constraint_name_true, constraint_name_false = constraint_names[constraint_comparison_num]
                axs[-1].set_xlabel(f'Time when {constraint_name_true} (All Solvers)')
                axs[-1].set_ylabel(f'Time when {constraint_name_false} (All Solvers)')
            else:
                axs[-1].set_xlabel(f'Time when constraint {constraint_comparison_num} is True (All Solvers)')
                axs[-1].set_ylabel(f'Time when constraint {constraint_comparison_num} is False (All Solvers)')

            axs[-1].set_xlim([0, self.x_max])
            axs[-1].set_ylim([0, self.y_max])
            axs[-1].grid(self.grid)

        plt.tight_layout()
        plt.show()


if __name__ == '__main__':
    time_instances_file_path = '../time-record/particular_hard_instance_time_record/argyle_time.txt'
    constraint_names = [("classic","argyle"),
                        ("distinct","PbEq"),
                        ("percol","inorder"),
                        ("is_bool","is_num"),
                        ("prefill","no_prefill"),
                        ("gen_time","solve_time")]
    plotter = ConstraintPlotter(time_instances_file_path)
    plotter.set_graph_properties(x_max=5,y_max=5)
    plotter.plot_constraints_comparison(1, solvers=["z3", "cvc5"],  combined_plot=True, constraint_names=constraint_names)