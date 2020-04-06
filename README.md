# Curry Frontend

The Curry frontend parses source files (`.curry`), emits errors and
warnings, performs various checks and transformations and 
generates FlatCurry (`.fcy`, `.fint`) or AbstractCurry (`.acy`, `.uacy`) amonst other formats.

The project originated from a modified version of the
Münster-Curry-Compiler (MCC) for use as a frontend in PAKCS.

## Requirements

* `cabal-install`
* A recent version of the `curry-base` package, installed locally

## Building

To build the project, run

> cabal v1-build

## Running

To run the project, you can use

> cabal v1-run

Alternatively, you can launch the built executable manually from `dist/build/curry-frontend`.

## Usage

For a detailed overview of the available options, you can use:

> curry-frontend --help

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
  
  > export PAKCS_LIB=[pakcs path]/pacs/lib:[pakcs path]/pacs/lib/meta:...

  where `[pakcs path]` is the directory containing the PAKCS distribution.

- In contrast to PAKCS, the frontend allow use of anonymous variables
  (denoted by an underscore `_`) in type declarations, e.g.
  
  ```curry
  data T _ = c
  ```

## Known Issues

- Lambda-, do-, if-, case-, oder let-Ausdrücke, die in Argumenten von
  Funktionsaufrufen verwendet werden, müssen immer geklammert werden.

- 'let'-Anweisungen dürfen nicht folgendes Layout besitzen:

           let x = <expr>
               in ...

- Die Regeln einer Funktionsdeklaration müssen immer zusammenstehen, d.h.
  nicht durch andere Deklarationen unterbrochen werden.

- Es ist bislang nicht möglich, den Konstruktor für leere Listen [], sowie 
  den Unit-Konstruktor () zu qualifizieren (z.B. führt 'prelude.[]' zu 
  einem Fehler). Der Listenkonstruktor (:), sowie Tupel-Konstruktoren
  dagegen sind qualifizierbar.

- FlatXML-Übersetzungen können derzeit mittels der Funktionen aus dem
  PAKCS-Modul "FlatXML" noch nicht eingelesen werden, da es Unstimmigkeiten
  zwischen dem generierten und den erforderlichen Formaten gibt.

- Bei der Erzeugung von typgeprüftem AbstractCurry können die im Quelltext
  verwendeten Bezeichner für Typvariablen nicht ins AbstractCurry-Programm
  übernommen werden. Stattdessen generiert der Übersetzer neue
  Bezeichner.

- Bei der Erzeugung von ungetyptem AbstractCurry werden Typsynonyme in
  Typsignaturen von Funktionen nicht dereferenziert.

- Das Frontend gibt derzeit noch keinerlei Warnungen aus.
