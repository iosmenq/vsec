# vsec
VSecure mini file encryption via iOS binary [THIS IOS BINARY NEEDS A JAILBREAK]

**ENCRYPT A FILE: vsec -e -pass "-d -pass "Password" -in file.txt -out file.vsec**

**DECRYPT A FILE: vsec -d -pass "Password" -in file.vsec -out decrypted.txt**

**YOU CAN COPY THE BINARY FILE TO /usr/bin or /usr/sbin**

**USE THE COMMAND ON THE SIDE FOR MORE FEATURES: vsec or vsec --help**

**BUILD NEED CLANG!!!**

**BUILD COMMAND: clang -O2 -Wall -Wextra -o vsec vsec.c -framework Security -framework CoreFoundation**
