var require = require("requirejs");
var requestjs = require("request");
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

function fromList(l0,fromElt){
  var a = [];
  var i = 0;
  function go(l) {
    l({"[]":  function() { }
      ,"_∷_": function(x,xs) { a[i] = fromElt(x); i++; go(xs) } });
  }
  go(l0);
  Object.freeze(a);
  return a
}

function objectFromList(l0,key,val) {
  var o = {};
  function go(l) {
    l({"[]":  function() { }
      ,"_∷_": function(x,xs) { o[key(x)] = val(x); go(xs) } });
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

m["fromJSBool"] = fromJSBool;
// m["fromJSArray"] = fromJSArray;
// m["fromList"] = fromList;
m["fromValue"] = fromValue;
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
  if (typeof(n) == "number") {
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
  return fromList(x,id).join("")
}

var fresh_port = 20000; // we hope is fresh
function next_port(){
  return (fresh_port += 1);
}

var localIP = "127.0.0.1";

function q(x) {
  return '"' + x + '"'
}

function uq(x) {
  if (typeof(x) == "string") {
    return x.substring(1, x.length - 1)
  } else {
    return x
  }
}

function post(tokens,dest,query,cb) {
  var h = {};
  var token = tokens[dest];
  if (token) { h["x-token"] = token };
  if (query) { h["x-query"] = q(query) };
  requestjs.post({"uri": dest, "headers": h}, function (error, response, body) {
    if (error) { throw error };
    if (response.statusCode == 200) {
      tokens[dest] = response.headers["x-token"];
      cb(uq(response.headers["x-response"]))
    } else {
      throw ("Unexpected status code: " + response.statusCode + ". Body: " + response.body)
    }
  })
  /*
  host, port, path ... dest
  http.request({"method": "post", "uri": dest, "headers": h}, function (response) {
    if (response.statusCode == 200) {
      tokens[dest] = response.headers["x-token"];
      cb(uq(response.headers["x-response"]))
    } else {
      response.setEncoding('utf8');
      response.on('data', function (chunk) {
        console.log('BODY: ' + chunk);
      });
      throw ("Unexpected status code: " + response.statusCode)
    }
  })
  */
}

// server : (ip port : String)(proc : Proc String String)
//          (callback : HTTPServer → (uri : String) → JSCmd) → JSCmd
function server(ip,port,initServer,callback){
  var sessions = {};
  var fresh_session = 0;
  var seed = crypto.randomBytes(32);
  console.log(seed);
  var uri = "http://" + ip + ":" + port + "/";
  var clientTokens = {};
  function new_session(o){
    // TODO atomic
    var session_num = fresh_session;
    fresh_session += 1;
    var token = sha256(seed + ":" + session_num);
    sessions[token] = o;
    o.token = token;
    // TODO timestamp/expiration
    // setTimeout(cb, ms)
    return token
  }
  function handle_request(req,res) {
    var query = uq(req.headers["x-query"]);
    function err(code,msg){
      res.writeHead(code);
      res.end(msg)
    }
    function ok(msg){
      if (msg) {
        res.writeHead(200,
            {"Content-Length": msg.length
            ,"Content-Type":   "text/plain"});
        res.end(msg)
      } else {
        res.writeHead(200);
        res.end()
      }
    }
    function input(d,k){
      if (typeof(d) == "string") {
        console.log("server [" + uri + "] d=" + d + " query=" + q(query));
        if (query) {
          err(400, "x-query present and typeof(d) == string")
        } else {
          post(clientTokens, d, null, function (resp) {
            go(k(resp))
          })
        }
      } else {
        if (query) {
          console.log("server [" + uri + "] receives: " + q(query));
          res.setHeader("x-token", new_session({"callback": k(query)}));
          ok()
        } else {
          err(400, "[server wants to 'input'] x-query expected")
        }
      }
    }
    function output(d,msg,k){
      if (query) {
        err(400, "[server wants to 'output'] No x-query expected")
      } else if (typeof(d) == "string") {
        console.log("server [" + uri + "] sends: " + q(msg) + " to: " + d);
        post(clientTokens,d,msg,function (resp) {
          go(k)
        })
      } else {
        console.log("server [" + uri + "] sends: " + q(msg));
        res.setHeader("x-token", new_session({"callback": k}));
        res.setHeader("x-response", q(msg));
        ok()
      }
    }
    function start(proc, k) {
      console.log("client start a new process");
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
      var req_token = req.headers["x-token"];
      if (!req_token) { // no token, initialize
        go(initServer)
      } else { // token present in request
        var session = sessions[req_token];
        if (session) { // valid token
          go(session.callback)
        } else {
          err(404, "invalid token")
        }
      }
    } else {
      err(404, "not a POST")
    }
  }
  var http_server = http.createServer(handle_request);
  http_server.listen(port, ip);
  console.log("Server running at " + uri);
  callback(http_server, uri)
}

// client : Proc String String → JSCmd → JSCmd
function client(clientInit,cb){
  var tokens = {};
  function input(dest,k) {
    post(tokens,dest,null, function (resp) {
      console.log("client receives: " + resp + " from: " + dest);
      go(k(resp))
    })
  }
  function output(dest,query,k) {
    console.log("client sends: " + query + " to: " + dest);
    post(tokens,dest,query, function (resp) {
      go(k)
    })
  }
  function start(proc, k) {
    console.log("client start a new process");
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
