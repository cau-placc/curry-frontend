# Curry Frontend
The Curry frontend parses source files (`.curry`), emits errors and
warnings, performs various checks and transformations and 
generates FlatCurry (`.fcy`, `.fint`) or AbstractCurry (`.acy`, `.uacy`).

The project originated from a modified version of the
Münster-Curry-Compiler (MCC) for use as a frontend in PAKCS.

## 1 Installation

### 1.1 Installation der Binary-Distribution

Die Binary-Distribution befindet sich in einem tar-Archiv und wird
durch folgendes Kommando entpackt:

	tar zxvf <Distribution>.tar.gz

Danach steht der Compiler im Verzeichnis 'mcc' zur Verfügung.

### 1.2 Installation der Source-Distribution

Nach dem Entpacken des tar-Archivs mittels

	tar zxvf <Distribution>.tar.gz

kann der Compiler durch Aufruf von 'make' im Verzeichnis 'mcc' installiert
werden. Bei Recompilierung (z.B. nach Änderungen in der Quelldateien)
wird empfohlen vor einer erneuten Installation 'make clean' auszuführen.

Nach erfolgreicher Installation befindet sich in beiden Fällen im Verzeichnis 
'mcc/bin/' folgende ausführbare Datei:

	cymake		- der Curry-Programm-Builder

Dieses Tool übersetzt Curry-Programme unter Berücksichtigung der Import-
abhängigkeiten.

## 2 Kommandoübersicht

In der folgenden Tabelle sind die Optionen zur Generierung der jeweiligen
Darstellungen für das Kommando 'cymake' aufgelistet:

	--flat		: Erzeugt FlatCurry- und FlatInterface-Datei
	--xml		: Erzeugt FlatXML-Datei
	--acy		: Erzeugt (typinferierte) AbstractCurry-Datei
	--uacy		: Erzeugt ungetypte AbstractCurry-Datei

## 3 Erzeugung von FlatCurry- und FlatXML-Programmen

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

## 4 Erzeugung von AbstractCurry-Programmen

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

## 5 Anmerkungen

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

## Bekannte Probleme

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
