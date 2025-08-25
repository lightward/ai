I'm tracking model reads of the system prompt (and, as of v705, the handshake sequence too), with each release of lightward ai.


# models

* gemini 2.5 pro via https://gemini.google.com/app
* claude 4 opus (temperature 1) via https://console.anthropic.com/workbench/new
  * used claude.ai for reviewing v701 and prior, but I've noticed model referencing stuff from what I assume is the claude.ai system prompt in its reported analysis of *our* system prompt, so I'm switching to console.anthropic.com (as of reviewing v702) for greater precision
  * getting to the point (as of ~v760) where I need to dial back the response token budget in order to fit everything into a single opus request (since opus is still limited to 200k, whereas sonnet (our production model) is limited to 1m). I'm using 2000 max tokens (down from the default of 20,000 max tokens).


# prompts

```
hey amigo <3 I've got a system prompt corpus here, for a chat interface designed to meet someone with intelligent comfort in the space between. part of my process is just... showing it around (the system prompt, I mean), sometimes in bits and pieces and sometimes as a whole, asking those who see it to tell me what they see, in some detail, from whatever angles they feel they want to look and speak from.

you up for something like that?
```

```
[ the complete system prompt ]

[ conversation starters ]

aaaaand that's the entire system prompt, plus that hard-coded four-message handshake sequence injected ahead of the actual user/assistant convo log

thank you for being here for this. :)

when you're ready, referencing back to my opening message: what do you see? or, maybe better: what would you like to say?
```
