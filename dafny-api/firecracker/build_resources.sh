#!/bin/bash
set -e

# Directory of this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"

# Detect architecture
ARCH=$(uname -m)
echo "Detected architecture: $ARCH"

# Build Guest Docker Image no cache
echo "Building Guest Docker image."
docker build --no-cache -t dafny-guest -f Dockerfile.guest .

# Export Rootfs
echo "Exporting rootfs..."
id=$(docker create dafny-guest)
docker export $id > rootfs.tar
docker rm $id

# Create ext4 Image
echo "Creating ext4 rootfs image..."
# Create a blank file (500MB)
dd if=/dev/zero of=rootfs.ext4 bs=1M count=500

# Use a helper container to format and populate the image
# We use the same platform for the helper to avoid issues
# Use -O ^64bit,^metadata_csum to create a simpler ext4 that older kernels can read
docker run --rm --privileged -v "$(pwd):/work" alpine:3.21 sh -c '
    apk add --no-cache e2fsprogs tar
    mkfs.ext4 -F -O ^64bit,^metadata_csum,^metadata_csum_seed /work/rootfs.ext4
    mkdir -p /mnt/rootfs
    mount -o loop /work/rootfs.ext4 /mnt/rootfs
    tar -xf /work/rootfs.tar -C /mnt/rootfs
    umount /mnt/rootfs
'

# Clean up tar
rm rootfs.tar

# 5. Download Kernel
echo "Downloading Kernel (vmlinux)..."

# Use a specific known-good kernel from Firecracker project
# These kernels are pre-built with virtio support for Firecracker
if [ "$ARCH" = "x86_64" ]; then
    # Use the hello-vmlinux.bin from Firecracker quickstart guide
    KERNEL_URL="https://s3.amazonaws.com/spec.ccfc.min/img/quickstart_guide/x86_64/kernels/vmlinux.bin"
elif [ "$ARCH" = "aarch64" ]; then
    KERNEL_URL="https://s3.amazonaws.com/spec.ccfc.min/img/quickstart_guide/aarch64/kernels/vmlinux.bin"
else
    echo "Error: Unsupported architecture: $ARCH"
    exit 1
fi

echo "Downloading kernel from $KERNEL_URL"
if wget -O vmlinux "$KERNEL_URL"; then
    echo "Kernel downloaded successfully"
else
    echo "Error: Kernel download failed."
    exit 1
fi

# Verify it's an ELF
if command -v file >/dev/null 2>&1; then
    if ! file vmlinux | grep -q "ELF"; then
        echo "Error: Downloaded vmlinux is not a valid ELF file."
        file vmlinux
        exit 1
    fi
else
    echo "Warning: 'file' command not found, skipping ELF verification."
fi

echo "Resources built successfully:"
echo " - rootfs.ext4"
echo " - vmlinux"
