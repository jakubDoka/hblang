#!/bin/bash



if [[ -n "$IN_SCRIPT" ]]; then
	if ! command -v git >/dev/null 2>&1; then
		pacman -Syu --noconfirm
		pacman -S --noconfirm wget git diffutils afl++ screen
	fi

	if ! command -v zig >/dev/null 2>&1; then
		wget https://ziglang.org/download/0.14.0/zig-linux-x86_64-0.14.0.tar.xz
		tar -xf zig-linux-x86_64-0.14.0.tar.xz

		ln -s /root/zig-linux-x86_64-0.14.0/zig /usr/bin/
	fi

	if [[ ! -d /root/hblang ]]; then
		git clone --recursive https://git.ablecorp.us/mlokis/hblang
	fi


	echo core | tee /proc/sys/kernel/core_pattern
	cd hblang
	zig build test -Dfuzz-tests=true -Dfuzz-duration=$DURATION -Drefuzz=true -Doptimize=ReleaseSafe

	exit
fi


ssh -p $SSH_ARGS "export IN_SCRIPT=true; export DURATION=$DURATION; $(cat $0)"
scp -P $SSH_ARGS:/root/hblang/zig-out/fuzz_finding_tests.zig ./zig-out/fuzz_finding_tests.zig
