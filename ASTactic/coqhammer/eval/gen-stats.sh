#!/bin/bash

cd tools
make
cd ..
cd atp
../tools/stat , y,p , , false
cd ..
tools/stat -r , y,p , , false

echo "<table>" >> statistics.html
echo "<tr><th>reasy</th><th>rsimple</th><th>rcrush</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep reasy {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rsimple {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rcrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html

echo "<table>" >> statistics.html
echo "<tr><th>ryelles4</th><th>rblast</th><th>ryreconstr</th><th>rreconstr4</th><th>ryelles6</th><th>rexhaustive1</th><th>rscrush</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep ryelles4 {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rblast {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep ryreconstr {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rreconstr4 {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep ryelles6 {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rexhaustive1 {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rscrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html
