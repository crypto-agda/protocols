var require = require("requirejs");
var m = require("jAgda.runningtest.js");
var requestjs = require("request");
var http = require("http");
var sha256 = require("crypto-js/sha256");
var crypto = require("crypto");

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

var cat = m["_++_"];

var adderclient = m["client"];
var adder = m["adder"];

var cater = m["cater"];
var caterclient = m["cater-client"];

m["_++_"] = function (x) {
  return function (y) {
    return (x + y);
  };
};

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

function getRandomSeed(){
  return crypto.randomBytes(32);
}

function client(uri,token,c,cb){
  function post(query,cb) {
    var h = {};
    if (token) { h["x-token"] = token };
    if (query) { h["x-query"] = query };
    requestjs.post({"uri": uri, "headers": h}, function (error, response, body) {
      if (error) { throw error };
      if (response.statusCode == 200) {
        cb(response.headers["x-response"], response.headers["x-token"])
      } else {
        throw ("Unexpected status code: " + response.statusCode + ". Body: " + response.body)
      }
    })
  }
  function input(k) {
    console.log("client 'input'");
    post(null, function (resp, token) {
      client(uri,token,k(resp),cb)
    })
  }
  function output(query,k) {
    console.log("client 'output': " + query);
    post(query, function (resp, token) {
      client(uri,token,k,cb)
    })
  }
  function end() {
    console.log("client 'end'");
    post(null, function (resp, token) {
      cb()
    })
  }
  c({"input": input, "output": output, "end": end})
}


function server(ip,port,initServer){
  var sessions = {};
  var fresh_session = 0;
  var seed = getRandomSeed();
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
    function handle_this_request(s) {
      var session = {};
      var query = req.headers["x-query"];
      if (query) {
        s({"input":  function(k){
                       console.log("server 'input'");
                       session.callback = k(query);
                       res.setHeader("x-token",new_session(session));
                       ok()
                     }
          ,"output": function(msg,k){ err(400, "[server wants to 'output'] No x-query expected") }
          ,"end":    function()     { err(400, "[server wants to 'end'] No x-query expected") }});
      } else {
        s({"input":  function(k)    { err(400, "[server wants to 'input'] x-query expected") }
          ,"output": function(msg,k){
                       console.log("server 'output': " + msg);
                       session.callback = k;
                       res.setHeader("x-token",new_session(session));
                       res.setHeader("x-response", msg);
                       ok()
                     }
          ,"end":    function()     { ok() }});
      }
    }
    if (req.method === "POST") {
      var req_token = req.headers["x-token"];
      if (!req_token) { // no token, initialize
        console.log("no token, initialize");
        handle_this_request(initServer)
      } else { // token present in request
        console.log("token present in request: " + req_token);
        var session = sessions[req_token];
        if (session) { // valid token
          handle_this_request(session.callback)
        } else {
          err(404, "invalid token")
        }
      }
    } else {
      err(404, "not a POST")
    }
  }
  http.createServer(handle_request).listen(port, ip);
  console.log("Server running at http://" + ip + ":" + port + "/");
}

console.log("server(cater):");
server("127.0.0.1", 1337, cater);
console.log("client(caterclient):");
client("http://127.0.0.1:1337/",null,caterclient("Hello ")("World!"),function() { });
client("http://127.0.0.1:1337/",null,caterclient("Bonjour ")("monde!"),function() { });

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
