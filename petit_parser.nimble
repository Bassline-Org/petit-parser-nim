# Package

version       = "0.1.0"
author        = "mercuricchloride"
description   = "A nim implementation of PetitParser"
license       = "MIT"
srcDir        = "src"

# Dependencies

requires "nim >= 2.2.10"

import std/[os, strutils]

task clean, "clean binaries in tests/*.nim":
  for f in listFiles("tests"):
    if f.splitFile.ext == "":
      rmFile f
  for d in listDirs("tests"):
    if d.endsWith ".dSYM":
      rmDir d