@echo off
del results.txt

for /L %%i in ( 1, 1, %1% ) do (
	java -jar tester.jar -exec main -seed %%i -novis | tee -a results.txt
)

echo ""
cat results.txt | grep "Score"
