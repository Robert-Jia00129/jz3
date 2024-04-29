from setuptools import setup, find_packages


setup(
    name='jz3',
    version='0.1.7',
    packages=find_packages(),
    description='A simple wrapper for Z3 solver',
    long_description=open('README.md').read(),
    long_description_content_type='text/markdown',
    author='Sebastiaan Joosten, Zheng Robert Jia',
    author_email='jia00129@umn.edu',
    url='https://github.com/Robert-Jia00129/jz3',
    license='MIT',
    install_requires=[
        'z3-solver',
        'matplotlib',
    ],
    package_data={
        'jz3': ['solvers/*']
    },
    python_requires='>3.11',
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Intended Audience :: Developers',
        'Topic :: Software Development :: Libraries',
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.8',
    ],
)