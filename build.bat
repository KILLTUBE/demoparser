@ECHO OFF
SET PATH=%PATH%;mingw32\bin
i686-w64-mingw32-g++ -static -Wno-write-strings -D COD_VERSION=COD2_1_0 main.cpp -o cod2demo.exe 
pause