# Exact tree-decomposition 

This software computes a tree-decomposition of the smallerst width of
a given graph.  It is part of a submission to the tw-exact track of the first Parameterized Algorithms and Computational Experiments Challenge ([PACE 2016](https://pacechallenge.wordpress.com/track-a-treewidth/)).  For the graph and tree-decomposition file format, see this PACE site.  The algorithm is sequenctial and implemented in C99.

## Usage

Read the graph in the .gr format from the standard input and write the resulting tree-decomposition in the .td format. See the PACE site mentioned above for
these file formats.
```
./tw-ex
```
## Build

Run `make`. In case of problems, try 'make clean' and then 'make'.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details
