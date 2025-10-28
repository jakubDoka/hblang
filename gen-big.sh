#!/usr/bin/sh

mode=$1

gen() {
	for i in $(seq $count); do
		echo "func$i := fn(): void {"
		echo "	i := 0"
		echo "	while i < 10 {"
		echo "		j := 0"
		echo "		while j < 10 {"
		echo "			k := 0"
		echo "			while k < 10 {"
		echo "				func$((i - 1))()"
		echo "				k += 1"
		echo "			}"
		echo "			j += 1"
		echo "		}"
		echo "		i += 1"
		echo "	}"
		echo "}"
	done
	
	echo "func0 := fn(): void {"
	echo "}"
	echo "main := fn(): void {"
	echo "    func$count()"
	echo "}"
}

if [ "$mode" == "" ]; then
	gen
fi

if [ "$mode" == "m" ]; then
	rm -rf big-source
	mkdir big-source

	for j in $(seq $file_count); do
		gen > big-source/func$j.hb

		echo "mod$j := @use(\"big-source/func$j.hb\")"
	done

	echo "main := fn(): void {"
	for i in $(seq $file_count); do
		echo "    mod$i.main()"
	done
	echo "}"
fi
