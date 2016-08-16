# Exact treewidth

This software computes a tree-decomposition of the smallest width of a given graph.  It is part of a submission to the tw-exact track of the first Parameterized Algorithms and Computational Experiments Challenge ([PACE 2016](https://pacechallenge.wordpress.com/track-a-treewidth/)).  The algorithm is sequential and implemented in C99.

## Usage

Read the graph in the .gr format from the standard input and write the resulting tree-decomposition in the .td format to the standard output. See the PACE site linked above for
these file formats.
```
./tw-exact
```
## Build

Run `make`. In case of problems, try `make clean` and then `make`.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details
