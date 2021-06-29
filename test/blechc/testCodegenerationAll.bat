@REM  Copyright (c) 2020 - for information on the respective copyright owner
@REM  see the NOTICE file and/or the repository 
@REM  https://github.com/boschresearch/blech.
@REM 
@REM  Licensed under the Apache License, Version 2.0 (the "License");
@REM  you may not use this file except in compliance with the License.
@REM  You may obtain a copy of the License at
@REM 
@REM      http://www.apache.org/licenses/LICENSE-2.0
@REM 
@REM  Unless required by applicable law or agreed to in writing, software
@REM  distributed under the License is distributed on an "AS IS" BASIS,
@REM  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
@REM  See the License for the specific language governing permissions and
@REM  limitations under the License.

@echo off


REM find and call the VS developer prompt - if not already done - so we have access to fsi and cl
if defined VS goto :mktmp

rem store current path because the call of VS prompt may reset it and we need to get back
set "curpath=%cd%"

set WHERE="%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere"
for /f "tokens=*" %%i in ('%WHERE% -all -property installationPath') do set VS=%%i

REM enable Visual Studio Tools
call "%VS%\Common7\Tools\VsDevCmd.bat"

rem restore the working directory from which this script has been called
cd %curpath%

:mktmp
rem ensure there is a tmp directory and ensure it is empty
if NOT exist tmp mkdir tmp
del /Q /S tmp\*

rem finally run the code generation test

echo *** Run tests for Blech-C interface
dotnet run -- blech_c_interface tmp/blech_c_interface

echo *** Run tests for general programs
dotnet run -- programs tmp/programs

echo *** Run tests for entry point activities with parameters
dotnet run -- blechAccess tmp/blechAccess

echo *** Run tests for module imports
dotnet run -- modules tmp/modules

echo *** Run tests according to Scode analysis
dotnet run -- 88problemsbutastructaintone tmp/88problemsbutastructaintone

pause