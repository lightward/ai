# EVERYONE IS HERE, a slice, in its maintainer's sentences (2026-09-08). bin/counter seat assays/sheet.feature
model Sheet

a Role is one of: couple, planner, vendor, venue, party
a Page is one of: floorPlan, guestList, samePage, invoices, budget, guests, site, team, dayOf, tasks
a Ask is one of: guests, sheet, timeline, bach

the couple sees: every Page
the planner sees: floorPlan, guestList, samePage, invoices, team, dayOf, tasks
the vendor sees: floorPlan, samePage, invoices, team, dayOf, tasks
the venue sees: floorPlan, samePage, invoices, team, dayOf, tasks
the party sees: floorPlan, guestList, samePage, team, dayOf, tasks

the couple edits: every Page
the planner edits: floorPlan, guestList, invoices, team, dayOf, tasks
the vendor edits: invoices, dayOf, tasks
the venue edits: floorPlan, invoices, dayOf, tasks
the party edits: floorPlan, guestList, dayOf, tasks

a Room has: guests (a list of numbers), delivered (a list of numbers), timeline (a list of numbers), bach (a list of numbers)
the room reads: guests as guests, sheet as delivered, timeline as timeline, bach as bach

the couple hears: guests, sheet, timeline
the caterer hears: timeline, sheet
the best man hears: timeline, bach

a Room may: withBach (bach becomes the argument)
a Room may: withGuests (guests becomes the argument)
a Room may: withTime (timeline gets the argument first)

wall: withBach changes nothing the couple hears
wall: withBach changes nothing the caterer hears
wall: withGuests changes nothing the caterer hears
wall: withGuests changes nothing the best man hears

given demo is a Room with guests [2, 3, 1], delivered [], timeline [10, 11, 12], bach [42]
when demo withBach [43] is newBach
then the caterer hears [[10, 11, 12], []] in demo
then the best man hears [[10, 11, 12], [43]] in newBach
then the couple hears [[2, 3, 1], [], [10, 11, 12]] in newBach
