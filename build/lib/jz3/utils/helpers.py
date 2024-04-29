import os
import random

def shuffle_files(files_dir):
    """Shuffle all lines in each file in the specified directory."""
    for filename in os.listdir(files_dir):
        file_path = os.path.join(files_dir, filename)
        if os.path.isfile(file_path):
            with open(file_path, 'r') as file:
                lines = file.readlines()
            random.shuffle(lines)
            with open(file_path, 'w') as file:
                file.writelines(lines)

def remove_duplicates_files(files_dir):
    """Remove duplicate lines from each file in the specified directory."""
    for filename in os.listdir(files_dir):
        file_path = os.path.join(files_dir, filename)
        if os.path.isfile(file_path):
            with open(file_path, 'r') as file:
                lines = set(file.readlines())
            with open(file_path, 'w') as file:
                file.writelines(lines)

def shuffle_and_remove_duplicates_files(files_dir):
    """Remove duplicate lines and then shuffle the rest in each file in the specified directory."""
    for filename in os.listdir(files_dir):
        file_path = os.path.join(files_dir, filename)
        if os.path.isfile(file_path):
            with open(file_path, 'r') as file:
                lines = set(file.readlines())
            lines = list(lines)
            random.shuffle(lines)
            with open(file_path, 'w') as file:
                file.writelines(lines)


if __name__=='__main__':
    pass