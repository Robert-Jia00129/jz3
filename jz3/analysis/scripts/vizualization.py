import ast
import matplotlib.pyplot as plt
import numpy as np
import sqlite3

PROBLEM_COL_START_IDX = 2
PROBLEM_COL_END_IDX = 6
IS_SAT_COL_IDX = 6


class ConstraintPlotter:
    def __init__(self, file_path):
        '''Initializes the ConstraintPlotter with the given SQLite database file path.'''
        self.file_path = file_path
        self.parsed_data = self._parse_data()
        self.x_max = 5
        self.y_max = 5
        self.width = 10
        self.height = 5
        self.opacity = 0.6
        self.marker_size = None
        self.line_style = 'r--'
        self.grid = True
        self.idx2name = self.list_constraints()
    
    def set_graph_properties(self, x_max=5, y_max=5, width=10, height=5, opacity=0.6, marker_size=None,
                             line_style='r--', grid=True):
        '''Sets the properties for the graph visualization.'''
        self.x_max = x_max
        self.y_max = y_max
        self.width = width
        self.height = height
        self.opacity = opacity
        self.marker_size = marker_size
        self.line_style = line_style
        self.grid = grid
    
    def _parse_data(self):
        '''Parses the SQLite database and organizes the data into a structured format.'''
        conn = sqlite3.connect(self.file_path)
        cursor = conn.cursor()
        cursor.execute("""
                       SELECT name, type
                       FROM sqlite_master
                       WHERE type IN ('table', 'view')
                         AND name NOT LIKE 'sqlite_%'
                       """)
        tables = cursor.fetchall()
        table_name = tables[0][0]
        cursor.execute('SELECT instance_id FROM ' + table_name)
        instances = cursor.fetchall()
        output = {}
        for i in range(instances[-1][0] + 1):
            cursor.execute('SELECT * FROM ' + table_name + ' WHERE instance_id=' + str(i))
            data = cursor.fetchall()
            output[i] = {'problem': {'grid': data[0][PROBLEM_COL_START_IDX:PROBLEM_COL_END_IDX],
                                     # 'index':data[0][3].split(', '),
                                     # 'try Val':data[0][4],
                                     # 'assert equals':data[0][5],
                                     'is sat': data[0][IS_SAT_COL_IDX]}
                         }
            for j in range(len(data)):
                output[i][(data[j][7], data[j][8], data[j][9], data[j][10], data[j][11])] = {
                    'cvc5': (data[j][12], data[j][13], data[j][14]), 'z3': (data[j][15], data[j][16], data[j][17])}
        parse_data = list(output.values())
        return parse_data
    
    def list_columns(self):
        '''Lists the columns in the database table along with their indices.'''
        conn = sqlite3.connect(self.file_path)
        cursor = conn.cursor()
        cursor.execute("""
                       SELECT name, type
                       FROM sqlite_master
                       WHERE type IN ('table', 'view')
                         AND name NOT LIKE 'sqlite_%'
                       """)
        tables = cursor.fetchall()
        table_name = tables[0][0]
        cursor.execute(f'PRAGMA table_info({table_name})')
        columns = cursor.fetchall()
        column_names = [col[1] for col in columns]
        output = {}
        for idx, name in enumerate(column_names):
            output[idx] = name
        return output
    
    def list_constraints(self):  # incomplete
        '''Lists the constraint columns in the database table along with their indices.'''
        conn = sqlite3.connect(self.file_path)
        cursor = conn.cursor()
        cursor.execute("""
                       SELECT name, type
                       FROM sqlite_master
                       WHERE type IN ('table', 'view')
                         AND name NOT LIKE 'sqlite_%'
                       """)
        tables = cursor.fetchall()
        table_name = tables[0][0]
        cursor.execute(f'PRAGMA table_info({table_name})')
        columns = cursor.fetchall()
        column_names = [col[1] for col in columns]
        output = {}
        for idx, name in enumerate(column_names[PROBLEM_COL_END_IDX + 1: -6]):  # {from (is_sat +1) to (cvc5_time -1).
            output[idx] = name
        print(output)
        return output
    
    def compare(self, solver, constraint):
        """Plots a comparison graph between two constraints for a specific solver using paired data."""
        mapping_to_index = {
            'classic': 0, 'distinct': 1, 'percol': 2, 'is_bool': 3, 'prefill': 4,
            'argyle': 0, 'PbEq': 1, 'inorder': 2, 'is_num': 3, 'no_prefill': 4
        }
        c = mapping_to_index[constraint]
        
        times_c1 = []  # constraint
        times_c2 = []  # complement
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
            'classic': 'argyle', 'distinct': 'PbEq', 'percol': 'inorder',
            'is_bool': 'is_num', 'prefill': 'no_prefill',
            'argyle': 'classic', 'PbEq': 'distinct', 'inorder': 'percol',
            'is_num': 'is_bool', 'no_prefill': 'prefill'
        }
        ax.set_title(f'Time Comparison: Constraint {constraint} vs {map_to_opposite[constraint]} ({solver})')
        
        ax.set_xlabel(f'Time when {constraint}')
        ax.set_ylabel(f'Time when {map_to_opposite[constraint]}')
        ax.set_xlim([0, self.x_max])
        ax.set_ylim([0, self.y_max])
        ax.grid(self.grid)
        
        plt.tight_layout()
        plt.show()
    
    def compare_idx(self, constraint_idx=None, solver='z3'):
        """Plots a comparison graph between two constraints for a specific solver using paired data.
        """
        if constraint_idx < 0 or constraint_idx >= len(self.idx2name):
            raise ValueError(f"Constraint index must be between 0 and {len(self.idx2name) - 1}")
        
        times_c1 = []  # constraint
        times_c2 = []  # complement
        
        for entry in self.parsed_data:
            processed_keys = set()
            for key in list(entry.keys()):
                if isinstance(key, tuple) and key not in processed_keys:
                    complement_list = list(key)
                    complement_list[constraint_idx] = not complement_list[constraint_idx]
                    complement_key = tuple(complement_list)
                    
                    if complement_key in entry:
                        if key[constraint_idx]:
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
        
        # Use idx2name to get the constraint name. This is soft code as idx2name is parsed from the database by taking idxs from PROBLEM_COL_END_IDX+1 to -6.
        name = self.idx2name[constraint_idx]
        
        ax.set_title(f'Time Comparison: Constraint {name} - {solver}')
        ax.set_xlabel(f'Time when constraint {name} is True')
        ax.set_ylabel(f'Time when constraint {name} is False')
        ax.set_xlim([0, self.x_max])
        ax.set_ylim([0, self.y_max])
        ax.grid(self.grid)
        
        plt.tight_layout()
        plt.show()


if __name__ == '__main__':
    time_instances_file_path = 'argyle_time.db'
    constraint_names = [("classic", "argyle"),
                        ("distinct", "PbEq"),
                        ("percol", "inorder"),
                        ("is_bool", "is_num"),
                        ("prefill", "no_prefill"),
                        ("gen_time", "solve_time")]
    plotter = ConstraintPlotter(time_instances_file_path)
    plotter.set_graph_properties(x_max=5, y_max=5)
    # plotter.plot_constraints_comparison(3, solvers=["z3", "cvc5"],  combined_plot=True, constraint_names=constraint_names)
    # plotter.plot_constraints_comparison(1, solvers=["z3","cvc5"],  combined_plot=False, constraint_names=constraint_names)
    print(plotter.list_columns())
    print(plotter.list_constraints())
    plotter.compare('z3', 'distinct')
    plotter.compare_idx(1)