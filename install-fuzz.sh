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
	else
		(cd hblang && git config pull.rebase true && git pull)
	fi

	echo core | tee /proc/sys/kernel/core_pattern

	SERVICE_NAME="hblang-fuzzer"
	COMMAND="zig build fuzz -Dfuzz-duration=$DURATION -Doptimize=ReleaseSafe"
	WORKING_DIR="/root/hblang"

	UNIT_FILE="[Unit]
	Description=Custom Service
	After=network.target

	[Service]
	Type=oneshot
	RemainAfterExit=true
	ExecStart=$COMMAND
	WorkingDirectory=$WORKING_DIR
	User=$USER

	[Install]
	WantedBy=multi-user.target"

	echo "$UNIT_FILE" > /etc/systemd/system/$SERVICE_NAME.service

	systemctl daemon-reload
	systemctl enable $SERVICE_NAME
	systemctl stop   $SERVICE_NAME 
	systemctl start  $SERVICE_NAME

	exit
fi


ssh -p $SSH_ARGS "export IN_SCRIPT=true; export DURATION=$DURATION; $(cat $0)"

sleep $(($DURATION + 3))
scp -P $SSH_ARGS:/root/hblang/zig-out/fuzz_finding_tests.zig ./src/fuzz_finding_tests.zig
