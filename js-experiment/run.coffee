require     = require "requirejs"
protocols   = require "protocols"
main_module = require ("jAgda." + process.argv[2])
protocols.runJSCmd main_module.main
