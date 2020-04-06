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
--flat  : Generate a FlatCurry and FlatInterface file
--xml   : Generate a FlatXML file
--acy   : Generate a (type-inferred) AbstractCurry file
--uacy  : Generate an untyped AbstractCurry file
```

#### Generation of FlatCurry and FlatXML files

Die Übersetzung eines Curry-Programms 'file.curry', sowie sämtlicher
importierter Module nach FlatCurry bzw. FlatInterface, bewirkt folgendes
Kommando:

	cymake --flat <filename>

Hierdurch werden die Dateien mit den entsprechenden Endungen ".fcy" und
".fint" generiert. Der Dateiname <filename> kann hierbei mit oder ohne 
Endung ".curry" bzw. ".lcurry" angegeben werden.

Die analogen Übersetzungen in die FlatXML-Darstellung bewirkt folgendes
Kommando:

	cymake --xml <file name>

Die hierdurch generierte Flat-XML-Datei hat die Endung '_flat.xml'.

#### Generation of AbstractCurry files

Die Übersetzung eines Curry-Programms 'file.curry' nach (typgeprüftem)
AbstractCurry bewirkt folgendes Kommando:

	cymake --acy <filename>

Hierdurch wird die entsprechende Datei (mit der Endung ".acy") generiert.
Der Dateiname <filename> kann hierbei mit oder ohne Endung ".curry" bzw.
".lcurry" angegeben werden.

Ungetypte, bzw. typsignierte AbstractCurry-Programme werden mit folgendem
Kommando generiert:

	cymake --uacy <filename>

Die hierdurch generierte Datei besitzt die Endung ".uacy".

Die Generierung des ungetypten AbstractCurry-Programms findet ohne
Typüberprüfung statt (d.h. auch Programme mit Typfehlern werden übersetzt).
Alle Funktionen besitzen entweder die im Quellprogramm angegebenen Typsignatur,
oder, sofern diese nicht vorhanden ist, den Dummy-Typ "prelude.untyped".

In beiden Fällen werden für die Übersetzung FlatCurry-Dateien 
für alle importierten Module erzeugt. Dies ist notwendig, da die 
entsprechenden Interfaces für die Typinferenz (nur im Fall der getypten 
AbstractCurry-Generierung) und die statisch-semantische Analyse benötigt 
werden.

## Remarks

- Um die PAKCS-Bibliotheken (insbesondere die Prelude) für Übersetzungen 
  nutzen zu können muß die Umgebungsvariable 'PAKCS_LIB' auf die
  entsprechenden Pfade verweisen, z.B. mittels

	export PAKCS_LIB=<pakcs path>/pacs/lib:<pakcs path>/pacs/lib/meta:...

  wobei <pakcs path> das Verzeichnis ist, das die PAKCS-Distribution
  enthält.

- Im Gegensatz zu PAKCS erlaubt das Frontend die Verwendung anonymer
  Variablen (dargestellt durch dem Unterstrich '_') in Typdeklarationen,
  z.B.

	data T _ = C

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
