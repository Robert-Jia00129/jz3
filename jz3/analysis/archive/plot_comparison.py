import ast
import matplotlib.pyplot as plt
import numpy as np
import sqlite3


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
        conn = sqlite3.connect(self.file_path)
        cursor = conn.cursor()
        cursor.execute("""
            SELECT name, type FROM sqlite_master 
            WHERE type IN ('table', 'view') AND name NOT LIKE 'sqlite_%'
        """)
        tables = cursor.fetchall()
        table_name = tables[0][0]
        cursor.execute('SELECT instance_id FROM '+table_name)
        instances = cursor.fetchall()
        output = {}
        for i in range(instances[-1][0]+1):
            cursor.execute('SELECT * FROM '+table_name+' WHERE instance_id='+str(i))
            data = cursor.fetchall()
            output[i] = {'problem':{'grid':data[0][2], 
                                    'index':data[0][3].split(', '),
                                    'try Val':data[0][4],
                                    'assert equals':data[0][5],
                                    'is sat':data[0][6]}
                                    }
            for j in range(len(data)):
                output[i][(data[j][7],data[j][8],data[j][9],data[j][10],data[j][11])] = {'cvc5':(data[j][12],data[j][13],data[j][14]),'z3':(data[j][15],data[j][16],data[j][17])}
        parse_data = list(output.values())
        return parse_data

    def plot_constraints_comparison(self, constraint_comparison_num, solvers=None, combined_plot=False, constraint_names=None):
        times_constraint_true = {}
        times_constraint_false = {}
        combined_times_true = []
        combined_times_false = []

        for entry in self.parsed_data:
            processed_keys = set()  # To keep track of processed keys
            for key in list(entry.keys()):
                if key not in processed_keys and isinstance(key, tuple):
                    # Create the complement key
                    complement_key = list(key)
                    complement_key[constraint_comparison_num] = not key[constraint_comparison_num]
                    complement_key = tuple(complement_key)
                    if complement_key in entry:
                        # Determine which is the True key and which is the False key
                        true_key, false_key = (key, complement_key) if key[constraint_comparison_num] else (
                        complement_key, key)

                        true_data = entry[true_key]
                        false_data = entry[false_key]

                        for solver_key in true_data:
                            if solver_key != 'smt_path' and (solvers is None or solver_key in solvers):
                                time_true = true_data[solver_key][0]
                                time_false = false_data[solver_key][0]

                                if solver_key not in times_constraint_true:
                                    times_constraint_true[solver_key] = []
                                if solver_key not in times_constraint_false:
                                    times_constraint_false[solver_key] = []

                                times_constraint_true[solver_key].append(time_true)
                                combined_times_true.append(time_true)

                                times_constraint_false[solver_key].append(time_false)
                                combined_times_false.append(time_false)

                        processed_keys.add(true_key)
                        processed_keys.add(false_key)

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
                    if ele > self.y_max:
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
    def compare(self, solver, constraint):
        """Plots a comparison graph between two constraints for a specific solver using paired data."""
        mapping_to_index = {
            'classic': 0, 'distinct': 1, 'percol': 2, 'is_bool': 3, 'prefill': 4,
            'argyle': 0, 'PbEq': 1, 'inorder': 2, 'is_num': 3, 'no_prefill': 4
        }
        c = mapping_to_index[constraint]
        
        times_c1 = [] # constraint
        times_c2 = [] # complement
        for entry in self.parsed_data:
            processed_keys = set()
            for key in list(entry.keys()):
                if isinstance(key, tuple) and key not in processed_keys:
                    complement_list = list(key)
                    complement_list[c] = not complement_list[c]
                    complement_key = tuple(complement_list)
                    
                    if complement_key in entry:
                        if key[c]:
                            true_key, false_key = key, complement_key
                        else:
                            true_key, false_key = complement_key, key
                        if solver in entry[true_key] and solver in entry[false_key]:
                            time_true = entry[true_key][solver][0]
                            time_false = entry[false_key][solver][0]
                            times_c1.append(time_true)
                            times_c2.append(time_false)
                        processed_keys.add(key)
                        processed_keys.add(complement_key)

        min_length = min(len(times_c1), len(times_c2))
        times_c1 = times_c1[:min_length]
        times_c2 = times_c2[:min_length]

        fig, ax = plt.subplots(figsize=(self.width, self.height))
        times_c1_clipped = np.clip(times_c1, 0, self.x_max)
        times_c2_clipped = np.clip(times_c2, 0, self.y_max)

        ax.scatter(times_c1_clipped, times_c2_clipped, 
                alpha=self.opacity, 
                s=self.marker_size)

        ax.plot([0, self.x_max], [0, self.y_max], self.line_style)
        map_to_opposite = {
            'classic':'argyle', 'distinct':'PbEq', 'percol':'inorder', 
            'is_bool':'is_num', 'prefill':'no_prefill',
            'argyle':'classic', 'PbEq':'distinct', 'inorder':'percol', 
            'is_num':'is_bool', 'no_prefill':'prefill'
        }
        ax.set_title(f'Time Comparison: Constraint {constraint} vs {map_to_opposite[constraint]} ({solver})')
        
        ax.set_xlabel(f'Time when {constraint}')
        ax.set_ylabel(f'Time when {map_to_opposite[constraint]}')
        ax.set_xlim([0, self.x_max])
        ax.set_ylim([0, self.y_max])
        ax.grid(self.grid)

        plt.tight_layout()
        plt.show()
if __name__ == '__main__':
    time_instances_file_path = 'argyle_time.db'
    constraint_names = [("classic","argyle"),
                        ("distinct","PbEq"),
                        ("percol","inorder"),
                        ("is_bool","is_num"),
                        ("prefill","no_prefill"),
                        ("gen_time","solve_time")]
    plotter = ConstraintPlotter(time_instances_file_path)
    plotter.set_graph_properties(x_max=5,y_max=5)
    # plotter.plot_constraints_comparison(3, solvers=["z3", "cvc5"],  combined_plot=True, constraint_names=constraint_names)
    plotter.plot_constraints_comparison(1, solvers=["z3","cvc5"],  combined_plot=False, constraint_names=constraint_names)
    plotter.compare('z3','distinct')
