define ["exports"
       ,"request"
       ,"http"
       ,"crypto-js/sha256"
       ,"crypto"],
       (exports
       ,request
       ,http
       ,sha256
       ,crypto) ->

  fresh_port = 20000 # we hope is fresh
  next_port = () -> ++fresh_port

  localIP = "127.0.0.1"

  post = (tokens, dest, query, cb) ->
    h = {}
    token = tokens[dest]
    h.token = token if token
    h.query = query if query
    request.post {uri: dest, json: h}, (error, response, body) ->
      throw error if error
      if response.statusCode isnt 200
        throw "Unexpected status code: #{response.statusCode}. Body: #{body}"
      else
        tokens[dest] = body.token
        cb body.response

  # server : (ip port : String)(proc : Proc String String)
  #          (callback : HTTPServer → (uri : String) → JSCmd) → JSCmd
  server = (ip, port, init_server, callback) ->

    server_tokens = {}
    client_tokens = {}
    server_token_num = 0
    seed = crypto.randomBytes 32
    console.log seed
    uri = "http://#{ip}:#{port}/"

    new_token = (cb) ->
      token = sha256 "#{seed}:#{server_token_num++}"
                .toString()
      server_tokens[token] =
        callback: cb
        token:    token
      # TODO timestamp/expiration
      # setTimeout(cb, ms)
      token

    handle_request = (req, res) ->

      err = (code, msg) ->
        res.writeHead code
        res.end msg

      ok = (msg) ->
        s = JSON.stringify msg
        res.writeHead 200,
            "content-length": s.length
            "content-type":   "application/json"
        res.end s

      body = ""
      query = null

      input = (d, k) ->
        if d isnt ""
          if query
            err 400, "query present but destination URI is not"
          else
            console.log "[#{uri}] server needs a query from dest: #{d}"
            post client_tokens, d, null, (resp) ->
              go k resp
        else
          if query
            console.log "[#{uri}] server receives: #{JSON.stringify query}"
            ok
              token: new_token k query
          else
            err 400, "server wants to receive: a query field was expected"

      output = (d, msg, k) ->
        if query
          err 400, "server wants to send: no query field was expected"
        else if d isnt ""
          console.log "[#{uri}] server sends: #{JSON.stringify msg} to: #{d}"
          post client_tokens, d, msg, (resp) -> go k
        else
          console.log "[#{uri}] server sends: #{JSON.stringify msg}"
          ok
            token:    new_token k
            response: msg

      start = (proc, k) ->
        console.log "[#{uri}] server starts a new process"
        # TODO deallocate servers
        newPort = next_port()
        server localIP, newPort, proc, (http_server, newURI) ->
          go k newURI

      end = () ->
        err 400, "server already ended the protocol"

      error = (msg) -> err 400, msg

      go = (s) ->
        s
          input:  input
          output: output
          start:  start
          end:    end
          error:  error

      if req.method is "POST"

        req.on "data", (chunk) -> body += chunk

        req.on "end", () ->
          body = JSON.parse body

          if body
            query = body.query

            if body.token
              # token present in request
              session = server_tokens[body.token]
              if session # valid token
                go session.callback
              else
                err 404, "invalid token"
            else
              # no token, initialize
              go init_server
          else
            err 400, "invalid JSON body"

      else
        err 404, "not a POST"

    http_server = http.createServer handle_request
    http_server.listen port, ip
    console.log "[#{uri}] server running"
    callback http_server, uri

  # client : Proc String String → JSCmd → JSCmd
  client = (client_init, cb) ->
    tokens = {}
    input = (dest, k) ->
      post tokens, dest, null, (resp) ->
        console.log "client receives: #{JSON.stringify resp} from: #{dest}"
        go k resp

    output = (dest, query, k) ->
      console.log "client sends: #{JSON.stringify query} to: #{dest}"
      post tokens, dest, query, (resp) -> go k

    start = (proc, k) ->
      console.log "client starts a new process"
      # TODO deallocate servers
      newPort = next_port()
      server localIP, newPort, proc, (http_server, newURI) ->
        go k newURI

    end = () ->
      console.log "client ends"
      cb()

    error = (msg) -> err 400, msg

    go = (c) ->
      c
        input:  input
        output: output
        start:  start
        end:    end
        error:  error

    go client_init

  runJSCmd = (c) ->
    c
      server:      (ip, port, proc, cb) ->
                    server ip, port, proc, (http_server, uri) ->
                      runJSCmd cb(http_server)(uri)
      client:      (proc, cb) -> client proc, () -> runJSCmd cb
      end:         () -> { }
      assert:      (b, cb) ->
                      b
                        true:  () -> runJSCmd cb
                        false: () -> throw "assert false"
      console_log: (s, cb) -> console.log s; runJSCmd cb

  exports.server   = server
  exports.client   = client
  exports.runJSCmd = runJSCmd
  exports
