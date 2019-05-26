Applications of Cheerios
========================

Verdi integration for packet serialization
------------------------------------------

- VST for applying serializers to a Verdi system to produce a serialized system with equivalent guarantees

- Verified serialization and extraction for the following systems:

  * verdi-lockserv
  * verdi-raft
  * verdi-aggregation
  * ...

- figure out a way to integrate input/output serialization and communication with clients (via explicit binary interface definitions?)

  * cheerios has a json serializer that should work well with yojson's json type.
  * not sure what using another language for clients with verified input/output serialization would look like
  * using json/input and json/output conversion functions should work best.


- instead of serializing messages to an explicit buffer, instead serialize directly to a TCP socket?

  * avoids having to send the length of the buffer over the socket in the shim
  * requires rethinking the interface between Verdi systems and network shims

File serialization and filesystem interaction
---------------------------------------------

- use Cheerios to write data types to persistent storage

- lift guarantees from POSIX filesystems (http://www.tom-ridge.com/resources/doc/sosp_draft.pdf) or FSCQ (http://css.csail.mit.edu/fscq/) to Cheerios?

- There are various issues with file consistency in real-world filesystems (https://danluu.com/file-consistency/)

Verdi network semantics with a persistent store
-----------------------------------------------

- develop a Verdi network semantics that captures writing to/from persistent storage

- integrate Cheerios with system using new network semantics

- previous work on TransActors may be relevant (http://digitool.rpi.edu:8881/dtl_publish/37/12193.html)

- Current plan: extend handlers to also capture writes to disk (also requires changes to reboot function?). First, snapshot on every handler call. Then, log message receives/sends. More possibilities: disk reads, omit certain events from log.
