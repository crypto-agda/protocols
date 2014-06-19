var require = require("requirejs");
var request = require("request");
var http = require("http");
var sha256 = require("crypto-js/sha256");
var crypto = require("crypto");
var m = require("jAgda.runningtest.js");

function id(x) { return x }

var nil  = m["List"]["[]"];
var cons = m["List"]["_∷_"];
var tt   = m["𝟙"]["record"];

function fromJSBool(b) {
  return m["Bool"][(b)? "true" : "false"]
}

function fromBool(b) {
  return b({"true": function() { return true }, "false": function() { return false } })
}

function fromJSArray(a){
  var len = a.length;
  var l = nil;
  Object.freeze(l);
  for (var i = len - 1; i >= 0; i--) {
    l = cons(a[i])(l);
    Object.freeze(l)
  }
  return l
}

function fromList(l0, fromElt){
  var a = [];
  var i = 0;
  function go(l) {
    l({"[]":  function() { }
      ,"_∷_": function(x, xs) { a[i] = fromElt(x); i++; go(xs) } });
  }
  go(l0);
  Object.freeze(a);
  return a
}

function objectFromList(l0, key, val) {
  var o = {};
  function go(l) {
    l({"[]":  function() { }
      ,"_∷_": function(x, xs) { o[key(x)] = val(x); go(xs) } });
  }
  go(l0);
  Object.freeze(o);
  return o
}

function fromValue(v) {
  return v({"array":  function(l) { return fromList(l, fromValue) }
           ,"object": function(l) { return objectFromList(l, function(x) { return x["fst"] },
                                                             function(x) { return fromValue(x["snd"]) }) }
           ,"string": id
           ,"number": id
           ,"bool":   fromBool
           ,"null":   function() { return null }
           })
}

function onString(f) { return function(x) { if (typeof(x) === "string") { return f(x); } else { throw "onString(): not a string"; }; }; }
function onString2(f) { return function(x) { return function(y) {
    if (typeof(x) === "string" && typeof(y) === "string") {
        return f(x)(y)
    } else {
        throw "onString(): not a string";
    }; }; } }

m["fromJSBool"] = fromJSBool;
// m["fromJSArray"] = fromJSArray;
// m["fromList"] = fromList;
m["fromValue"] = fromValue;
m["onString"] = onString;
m["onString2"] = onString2;
//m["JSON-stringify"] = JSON.stringify;
//m["console-log"] = function(s) { return function(k) { return function() { console.log(s); k() } } }

/*
var zero = m["ℕ"]["zero"];
var suc  = m["ℕ"]["suc"];
var plus = m["_+_"];
function nat(n){
  if (n > 0) {
    return suc(nat(n - 1));
  } else {
    return zero;
  }
}
function fromNat(n){
  if (typeof(n) === "number") {
    return n;
  } else {
    return n({"zero": function()  { return 0; }
             ,"suc":  function(x) { return 1 + fromNat(x); } });
  }
}
*/

m["Σ"]["fst"] = function (y0) {
  return function (y1) {
  return function (x0) {
    return x0["fst"];
  }
  }
}

m["Σ"]["snd"] = function (y0) {
  return function (y1) {
  return function (x0) {
    return x0["snd"];
  }
  }
}

m["String▹List"] = function (x) {
  return fromJSArray(x.split(""))
}

m["List▹String"] = function (x) {
  return fromList(x, id).join("")
}

var fresh_port = 20000; // we hope is fresh
function next_port(){
  return (fresh_port += 1);
}

var localIP = "127.0.0.1";

function post(tokens, dest, query, cb) {
  var h = {};
  var token = tokens[dest];
  if (token) { h.token = token };
  if (query) { h.query = query };
  request.post({uri: dest, json: h}, function (error, response, body) {
    if (error) { throw error };
    if (response.statusCode === 200) {
      tokens[dest] = body.token;
      cb(body.response)
    } else {
      throw ("Unexpected status code: " + response.statusCode + ". Body: " + body)
    }
  })
}

// server : (ip port : String)(proc : Proc String String)
//          (callback : HTTPServer → (uri : String) → JSCmd) → JSCmd
function server(ip, port, initServer, callback){

  var server_tokens = {};
  var client_tokens = {};
  var server_token_num = 0;
  var seed = crypto.randomBytes(32);
  console.log(seed);
  var uri = "http://" + ip + ":" + port + "/";

  function new_token(o){
    var token = sha256(seed + ":" + server_token_num++).toString();
    server_tokens[token] = o;
    o.token = token;
    // TODO timestamp/expiration
    // setTimeout(cb, ms)
    return token
  }

  function handle_request(req, res) {

    function err(code, msg){
      res.writeHead(code);
      res.end(msg)
    }

    function ok(msg){
      var s = JSON.stringify(msg);
      res.writeHead(200,
          {"content-length": s.length
          ,"content-type":   "application/json"});
      res.end(s)
    }

    var body = "";
    var query = null;

    function input(d, k){
      if (typeof(d) === "string") {
        if (query) {
          err(400, "query present and typeof(d) is string")
        } else {
          console.log("[" + uri + "] server needs a query from dest: " + d);
          post(client_tokens, d, null, function (resp) {
            go(k(resp))
          })
        }
      } else {
        if (query) {
          console.log("[" + uri + "] server receives: " + JSON.stringify(query));
          ok({token: new_token({callback: k(query)})})
        } else {
          err(400, "server wants to receive: a query field was expected")
        }
      }
    }

    function output(d, msg, k){
      if (query) {
        err(400, "server wants to send: no query field was expected")
      } else if (typeof(d) === "string") {
        console.log("[" + uri + "] server sends: " + JSON.stringify(msg) + " to: " + d);
        post(client_tokens, d, msg, function (resp) {
          go(k)
        })
      } else {
        console.log("[" + uri + "] server sends: " + JSON.stringify(msg));
        ok({token: new_token({callback: k}), response: msg})
      }
    }

    function start(proc, k) {
      console.log("[" + uri + "] server starts a new process");
      // TODO deallocate servers
      var newPort = next_port();
      server(localIP, newPort, proc, function (http_server, newURI) {
        go(k(newURI))
      })
    }

    function end() {
      err(400, "server already ended the protocol")
    }

    function error(msg) {
      err(400, msg)
    }

    function go(s) {
      s({"input": input, "output": output, "start": start, "end": end, "error": error})
    }

    if (req.method === "POST") {

      req.on('data', function (chunk) { body += chunk });

      req.on('end', function () {
        body  = JSON.parse(body);

        if (body) {
          query = body.query;

          if (!body.token) { // no token, initialize
            go(initServer)
          } else { // token present in request
            var session = server_tokens[body.token];
            if (session) { // valid token
              go(session.callback)
            } else {
              err(404, "invalid token")
            }
          }
        } else {
          err(400, "invalid JSON body")
        }
      })

    } else {
      err(404, "not a POST")
    }

  }

  var http_server = http.createServer(handle_request);
  http_server.listen(port, ip);
  console.log("[" + uri + "] server running");
  callback(http_server, uri)
}

// client : Proc String String → JSCmd → JSCmd
function client(clientInit, cb){
  var tokens = {};
  function input(dest, k) {
    post(tokens, dest, null, function (resp) {
      console.log("client receives: " + JSON.stringify(resp) + " from: " + dest);
      go(k(resp))
    })
  }
  function output(dest, query, k) {
    console.log("client sends: " + JSON.stringify(query) + " to: " + dest);
    post(tokens, dest, query, function (resp) {
      go(k)
    })
  }
  function start(proc, k) {
    console.log("client starts a new process");
    // TODO deallocate servers
    var newPort = next_port();
    server(localIP, newPort, proc, function (http_server, newURI) {
      go(k(newURI))
    })
  }
  function end() {
    console.log("client ends");
    cb()
  }
  function error(msg) {
    err(400, msg)
  }
  function go(c) {
    c({"input": input, "output": output, "start": start, "end": end, "error": error})
  }
  go(clientInit)
}

function runJSCmd(c) {
  c({"server": function(ip, port, proc, cb) {
                 server(ip, port, proc, function(http_server, uri) {
                   runJSCmd(cb(http_server)(uri))
                 })
               }
    ,"client":      function(proc, cb) { client(proc, function() { runJSCmd(cb) }) }
    ,"end":         function () { }
    ,"console-log": function (s, cb) { console.log(s); runJSCmd(cb) }
    })
}

runJSCmd(m["main"](tt))
