#!/bin/bash
## A script for downloading cached state for Travis. This file is
## probably obsolete, since Travis is no longer supported.

set -e

pushd $HOME

wget https://www.strongspace.com/xrchz/public/cache.tar.xz

tar --extract --auto-compress --file=cache.tar.xz

popd
