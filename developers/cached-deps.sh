#!/bin/bash

set -e

pushd $HOME

wget https://www.strongspace.com/xrchz/public/cache.tar.xz

tar --extract --auto-compress --file=cache.tar.xz

popd
