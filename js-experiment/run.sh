#!/bin/bash -eu
main=runningtest
coffee -b -c libagda.coffee protocols.coffee
agda --js $main.agda
coffee -b run.coffee -- $main
