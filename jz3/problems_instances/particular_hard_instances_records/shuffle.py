import random

def shuffle_file_contents(filename):
    # Read the lines from the file
    with open(filename, 'r') as file:
        lines = file.readlines()

    # Shuffle the lines
    random.shuffle(lines)

    # Optional: Write the shuffled lines back to a file or return them
    with open(filename, 'w') as file:
        file.writelines(lines)

if __name__=='__main__':
    shuffle_file_contents('txt_file/hard_argyle_instances.txt')
    shuffle_file_contents('txt_file/hard_classic_instances.txt')
