#!/bin/sh

groff -t -e -mandoc -Tascii cghttpd.8 | col -bx > cghttpd.txt
groff -t -e -mandoc -Tps cghttpd.8 | ps2pdf - cghttpd.pdf
man2html < cghttpd.8 | sed 's/<BODY>/<BODY text="#0000FF" bgcolor="#FFFFFF" style="font-family: monospace;">/i' > cghttpd.html

