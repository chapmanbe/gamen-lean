#!/usr/bin/env bash
# Build the course project (and the gamen package it depends on) for lean4web.
cd "$(dirname "$0")"
lake build
