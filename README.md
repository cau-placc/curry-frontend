# Curry Frontend

The frontend lexes, parses, type-checks and transforms Curry source files into a variety of intermediate formats, including

* **FlatCurry** for program analyzers and backends
* **AbstractCurry** for program manipulation tools
* **HTML** for documentation

It is used by the two major Curry compilers, [PAKCS](https://git.ps.informatik.uni-kiel.de/curry/pakcs) and
[KiCS2](https://git.ps.informatik.uni-kiel.de/curry/kics2).

## Requirements

* Make sure that a recent version of Haskell Stack is installed on your computer

## Building

* To build the project, run `make`.
* To test the project, run `make runtests`.

The built executable will be located at `bin/curry-frontend`.

## Usage

For a detailed overview of the available options, you can use the following command:

`curry-frontend --help`

### Available Formats

```
--flat  : Generate a FlatCurry (.fcy) and FlatInterface (.fint) file
--xml   : Generate a FlatXML (_flat.xml) file
--acy   : Generate a (type-inferred) AbstractCurry (.acy) file
--uacy  : Generate an untyped AbstractCurry (.uacy) file
```

The generation of an untyped AbstractCurry program is performed without
type checking (i.e. programs with type checks will compile). All functions
will either have the type signature specified in the source or, if not
available, the dummy type `prelude.untyped`.

FlatCurry files will always be generated for the imported modules,
since the interfaces are required for static-semantic analysis and type
inference (only for typed AbstractCurry).

## Remarks

- To use the PAKCS libraries (especially for the `Prelude`), the environment
  variable `PAKCS_LIB` has to point to the correct paths, e.g. using
  
  `export PAKCS_LIB=[pakcs path]/pacs/lib:[pakcs path]/pacs/lib/meta:...`

  where `[pakcs path]` is the directory containing the PAKCS distribution.

- In contrast to PAKCS, the frontend allow use of anonymous variables
  (denoted by an underscore `_`) in type declarations, e.g.
  
  ```curry
  data T _ = c
  ```

## Known Issues

[See GitLab](https://git.ps.informatik.uni-kiel.de/curry/curry-frontend/-/issues)
