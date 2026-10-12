# Package

version       = "0.1.0"
author        = "mercuricchloride"
description   = "A nim implementation of PetitParser"
license       = "MIT"
srcDir        = "src"

# Dependencies

requires "nim >= 2.2.10"

task reader, "Build the bassline text reader for JavaScript into dist/":
  mkDir "dist"
  exec "nim js -d:nodejs -d:release --hints:off -o:dist/bassline_text.mjs src/petit_parser/js.nim"

import std/[os, strutils]

task clean, "clean binaries in tests/*.nim":
  for f in listFiles("tests"):
    if f.splitFile.ext == "":
      rmFile f
  for d in listDirs("tests"):
    if d.endsWith ".dSYM":
      rmDir d