!(import! &self (library pettaclaw-godel lib_mettaclaw))

!(once (initLoop))
!(once (initMemory))
!(once (initChannels))
!(once
  (let* (($msg (string-safe (repr (receive))))
         ($msgnew (prog1 (!= $msg (get-state &prevmsg))
                         (change-state! &prevmsg $msg)))
         ($humanmsg (lastMessageIsHuman))
         ($_ (if $msgnew
                 (if $humanmsg
                     (progn (change-state! &loops (maxLoops))
                            (change-state! &sleepInterval (sleepInterval))
                            (change-state! &last-heartbeat (get_time)))
                     _)
                 _))
         ($_hb (maybeHeartbeat))
         ($prompt (getContext))
         ($lastmessage (HUMAN-LAST-MSG: $msg
                       MESSAGE-IS-NEW: $msgnew
                       HUMAN-MESSAGE-ARMS-LOOP: $humanmsg))
         ($send (py-str ($prompt $lastmessage))))
    $send))
