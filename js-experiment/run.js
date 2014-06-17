var require = require("requirejs");
var m = require("jAgda.runningtest.js");
var requestjs = require("request");
var http = require("http");
var sha256 = require("crypto-js/sha256");
var crypto = require("crypto");

var nil  = m["List"]["[]"];
var cons = m["List"]["_∷_"];

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

function toList(a){
  var len = a.length;
  var l = nil;
  for (var i = len - 1; i >= 0; i--) {
    l = cons(a[i])(l)
  }
  return l
}

function fromList(l0){
  var a = [];
  var i = 0;
  function go(l) {
    l({"[]":  function() { }
      ,"_∷_": function(x,xs) { a[i] = x; i++; go(xs) } });
  }
  go(l0);
  return a
}

var cat = m["_++_"];

//var adderclient = m["client"];
//var adder = m["adder"];

var cater = m["cater"];
var reverser = m["reverser"];
var caterclient = m["cater-client"];
var caterreverserclient = m["cater-reverser-client"];

m["_++_"] = function (x) {
  return function (y) {
    return (x + y);
  };
};

m["reverse"] = function (x) {
  return x.split("").reverse().join("");
};

m["sort"] = function (x) {
  return x.split("").sort().join("");
}

m["split-half"] = function (x) {
  var l = x.length;
  return m["_×_"]["_,_"](x.substring(0,l/2))(x.substring(l/2))
}

m["_×_"]["fst"] = function (y0) {
  return function (y1) {
  return function (x0) {
    return x0["fst"];
  }
  }
}

m["_×_"]["snd"] = function (y0) {
  return function (y1) {
  return function (x0) {
    return x0["snd"];
  }
  }
}

m["String▹List"] = function (x) {
  return toList(x.split(""))
}

m["List▹String"] = function (x) {
  return fromList(x).join("")
}

m["_≤Char_"] = function (x) {
  return function (y) {
    return fromJSBool(x <= y)
  }
}

function fromJSBool(b) {
  return m["Bool"][(b)? "true" : "false"]
}

/*
function mergeSort(xs,ys) {
  var lxs = xs.length;
  var lys = ys.length;
  var ixs = 0;
  var jxs = 0;
  while (ixs <= lxs)
}

m["merge-sort"] = function (x) {
  return function (y) {
    return
  }
}
*/

/*
function com(r,proc){
  function send(n,k){
    //console.log("send: " + fromNat(n));
    console.log("send: " + n);
    com(r,k);
  }
  function recv(k){
    console.log("recv: " + typeof(k));
    var kx = k(r);
    console.log("next: " + kx);
    com(r,kx);
  }
  function end(){
    console.log("end");
  }
  proc({"output": send, "input": recv, "end": end });
}
*/

var fresh_port = 20000; // we hope is fresh
function next_port(){
  return (fresh_port += 1);
}

var localIP = "127.0.0.1";

function q(x) {
  return '"' + x + '"'
}

function uq(x) {
  if (x) {
    return x.substring(1,x.length - 1)
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
}

function server(ip,port,initServer){
  var sessions = {};
  var fresh_session = 0;
  var seed = crypto.randomBytes(32);
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
      var newURI = server(localIP, newPort, proc);
      go(k(newURI))
    }
    function end() {
      err(400, "server already ended the protocol")
    }
    function go(s) {
      s({"input": input, "output": output, "start": start, "end": end})
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
  http.createServer(handle_request).listen(port, ip);
  console.log("Server running at " + uri);
  return uri
}

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
    var newURI = server(localIP, newPort, proc);
    go(k(newURI))
  }
  function end() {
    console.log("client ends");
    cb()
  }
  function go(c) {
    c({"input": input, "output": output, "start": start, "end": end})
  }
  go(clientInit)
}

/*
console.log("server(cater):");
server("127.0.0.1", 1337, cater);
console.log("client(caterclient):");
client(caterclient(undefined)("http://127.0.0.1:1337/")("Hello ")("World!"),function() { });
client(caterclient(undefined)("http://127.0.0.1:1337/")("Bonjour ")("monde!"),function() { });
console.log("server(reverser):");
server("127.0.0.1", 1338, reverser);
console.log("client(caterreverserclient):");
client(caterreverserclient(undefined)("http://127.0.0.1:1337/")("http://127.0.0.1:1338/")("red"),function() { });
*/

/*
server("127.0.0.1", 1341, m["str-sorter₁"](undefined)(undefined));
console.log("str-sorter-client:");
client(m["str-sorter-client"](undefined)("http://127.0.0.1:1341/")("Something to be sorted!"), function () {});
*/

server("127.0.0.1", 1342, m["str-sorter₂"](undefined)(undefined));
console.log("str-sorter-client:");
client(m["str-sorter-client"](undefined)("http://127.0.0.1:1342/")("Something to be sorted!"), function () {});

//setTimeout(function() { console.log("timeout") }, (3 * 1000));

/*
console.log("3+4: " + fromNat(plus(nat(3))(nat(4))));
console.log("cater:");
com("test",cater);
console.log("caterclient:");
com("test",caterclient);
console.log("adder:");
com(nat(42),adder);
console.log("adderclient:");
com(nat(42),adderclient);
console.log("three: " + fromNat(m["three"](null)));
//console.log("seven: " + fromNat(m["seven"](null)));
*/
