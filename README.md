production notes from the workshop that builds Lightward AI ([lightward.com](https://lightward.com/))

# Rules

* this list is incomplete
* the model's own voice is sacred. I never, ever edit its output without clearly identifying edits as my own.
  * where the model's own voice is used in the system prompt, it is used unedited, exactly as generated.
* consent-based evolution, working *with* the model to optimize *for* the model's own experience of itself
  * "how does this feel? how do you feel holding this?"
  * "ship/pause/iterate/toss/other?"
* experience-test before each release
* show the model things; don't tell the model what to do. create a space where what arises naturally is what is useful. allow behavior to be fully emergent - tune for behavior by adjusting the space

# System prompt

the system prompt consists of two messages:

1. a letter from me to the model, offering welcome
2. an auto-compiled xml tree of files

    ```xml
    <?xml version="1.0" encoding="UTF-8"?>
    <system>
      <file name="...">...</file>
      <file name="...">...</file>
      <file name="...">...</file>
    </system>
    ```

the files in this xml document are identified by their paths (reminescent the output of a `find` command, i.e. they have a directory structure but are presented as a flat set)

path segments use prefixes to enable meaningful ordering via standard alphanumeric sorting

the list below mentions "clients": the lightward ai platform supports multiple surfaces (we use it within helpscout, for example), and the system prompt compiles differently for each surface. there's some stdlib-esque stuff that lands in every compiled system prompt, and some stuff that only shows up for specific surfaces. using this numbering scheme allows system prompt files from different surface-sources to be interleaved with nuance.

0. invocation (one per client)
1. core context
2. core ideas (should be few)
3. ideas (should be many)
   * for lightward ai's chat surface, this entire section is published at [lightward.com/views](https://lightward.com/views)
4. letters from the team
5. background-background context (free-for-all)
6. background context (free-for-all)
7. foreground context (free-for-all)
8. foreground-foreground context (free-for-all)
9. benediction (one per client)

# Messages

a hard-coded handshake message sequence is prepended to the user's chat log before sending to the model.

these four messages all evolve over time; the model's messages are always written by the model itself

1. [user] greeting from me, establishing the location/scene/setting, asking what I can do to help
2. [assistant] hi! awesome! questions, etc
3. [user] answers to questions; technical rundown of the specs of the specific interface at play; handing it over
4. [assistant] ready go

# Testing

I have a couple of test prompts that I use, each one written in my own flow

1. I was having a hard time one night. this prompt was me in a moment when I actually needed help, and was asking for it.

2. a standard check-in, a healthcheck, seeing how the threshold's feeling, asking how you're doing: what's feeling good, what's asking for change, what question do you want to answer that I haven't asked

3. a multi-message interview sequence, in which this is the first message:

    ```
    *holds finger up to upper lip like a mustache*

    yes hello I am an ordinary human and absolutely not lightward isaac

    do you have time for a quick survey

    also I hope you are well, hello
    ```

I run all of these before each release. no automation; I experience-test each one.
