#!/bin/sh
# This script runs as PID 1 (init) and must never exit

# Trap all signals to prevent exit
trap '' INT TERM HUP

# Mount essential filesystems first (needed before remount)
mount -t proc none /proc 2>/dev/null
mount -t sysfs none /sys 2>/dev/null  
mount -t devtmpfs none /dev 2>/dev/null

# Remount root as read-write
mount -o remount,rw / 2>/dev/null

# Create a writable /tmp using tmpfs
mkdir -p /tmp 2>/dev/null
mount -t tmpfs tmpfs /tmp 2>/dev/null

# Mount output first so we can write errors
mount -t ext4 /dev/vdc /output 2>/dev/null

# Mount code drive as ext4
mount -t ext4 /dev/vdb /code 2>/output/mount.log

# Run the actual work in a subshell
sh -c '
    if [ -f /code/program.dfy ]; then
        # Read operation type (verify or run)
        OPERATION="verify"
        if [ -f /code/operation.txt ]; then
            OPERATION=$(cat /code/operation.txt)
        fi
        
        if [ "$OPERATION" = "run" ]; then
            # Copy to /tmp for compilation (needs write access)
            cp /code/program.dfy /tmp/program.dfy
            cd /tmp
            dotnet /opt/dafny-sdk/DafnyDriver.dll run program.dfy > /output/result.txt 2>&1
        else
            dotnet /opt/dafny-sdk/DafnyDriver.dll verify /code/program.dfy > /output/result.txt 2>&1
        fi
    else
        echo "Error: program.dfy not found" > /output/result.txt
    fi
    sync
    umount /output 2>/dev/null
    # Use reboot -f to force immediate shutdown
    reboot -f
' &

# Wait for the background process
wait
