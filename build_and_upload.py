import os
import shutil
import subprocess
import argparse


def update_version(version):
    with open('setup.py', 'r') as file:
        setup_content = file.read()

    updated_setup_content = setup_content.replace(
        "version='0.1.0'",
        f"version='{version}'"
    )

    with open('setup.py', 'w') as file:
        file.write(updated_setup_content)


def build_library():
    # Remove previous build artifacts
    if os.path.exists('dist'):
        shutil.rmtree('dist')

    # Build the library
    subprocess.run(['python', 'setup.py', 'sdist', 'bdist_wheel'])


def upload_to_pypi():
    # Install twine if not already installed
    subprocess.run(['pip', 'install', 'twine'])

    api_key = os.getenv('PYPI_API_KEY')

    # Upload the library to PyPI
    subprocess.run(['twine', 'upload', '--username', '__token__', '--password', api_key, 'dist/*'])


def main():
    parser = argparse.ArgumentParser(description='Build and upload the library.')
    parser.add_argument('--version', required=True, help='Version number of the library')
    args = parser.parse_args()

    update_version(args.version)
    build_library()

    while True:
        choice = input("Do you want to upload the library to PyPI? (y/n): ")
        if choice.lower() == 'y':
            upload_to_pypi()
            break
        elif choice.lower() == 'n':
            break
        else:
            print("Invalid choice. Please enter 'y' or 'n'.")


if __name__ == '__main__':
    main()