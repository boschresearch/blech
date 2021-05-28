#!/bin/sh
if [ ! -d tmp ]; then
    mkdir tmp
fi

rm -rf tmp/*

echo '*** Run tests for Blech-C interface'
dotnet run -- blech_c_interface tmp/blech_c_interface

echo '*** Run tests for general programs'
dotnet run -- programs tmp/programs

echo '*** Run tests for entry point activities with parameters'
dotnet run -- blechAccess tmp/blechAccess

echo '*** Run tests for module imports'
dotnet run -- modules tmp/modules

echo '*** Run tests according to Scode analysis'
dotnet run -- 88problemsbutastructaintone tmp/88problemsbutastructaintone
