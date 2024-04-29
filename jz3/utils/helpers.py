import os
import random
import errno

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
    print(f'Finished for: ')
    for filename in os.listdir(files_dir):
        if not filename.startswith('.'):  # Skip hidden files
            file_path = os.path.join(files_dir, filename)
            if os.path.isfile(file_path):
                with open(file_path, 'r') as file:
                    lines = set(file.readlines())
                lines = list(lines)
                random.shuffle(lines)
                with open(file_path, 'w') as file:
                    file.writelines(lines)
            print(f"{filename} ", end='')
    print(f'\nFinished shuffling and removing duplicates for all files in {files_dir}')


def clean_dir(file_dir_lst):
    """Empties the contents of files in each specified directory without removing the files."""
    for dir_path in file_dir_lst:
        if os.path.exists(dir_path):
            for filename in os.listdir(dir_path):
                file_path = os.path.join(dir_path, filename)
                if os.path.isfile(file_path):
                    open(file_path, 'w').close()  # Open in write mode and immediately close to clear contents


def delete_dir(file_dir_lst):
    """Deletes each specified directory and its contents if it exists."""
    for dir_path in file_dir_lst:
        try:
            if os.path.exists(dir_path):
                for filename in os.listdir(dir_path):
                    file_path = os.path.join(dir_path, filename)
                    os.remove(file_path)
                os.rmdir(dir_path)
        except OSError as e:
            if e.errno != errno.ENOENT:  # No such file or directory
                raise  # Re-raise exception if a different error occurred


if __name__=='__main__':
    pass