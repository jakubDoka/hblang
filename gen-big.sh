#!/usr/bin/sh


for i in $(seq $count); do
	echo "func$i := fn(): void {"
	echo "    func$((i - 1))()"
	echo "}"
done

echo "func0 := fn(): void {"
echo "}"
echo "main := fn(): void {"
echo "    func$count()"
echo "}"
