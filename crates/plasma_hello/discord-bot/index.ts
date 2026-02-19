const TOKEN = "TODO_REPLACE_WITH_TOKEN"

import {
    Client,
    Events,
    GatewayIntentBits,
    Partials,
} from "discord.js"

async function get_client(): Promise<Client<true>> {
    const client = new Client({
        intents: [
            GatewayIntentBits.Guilds,
            GatewayIntentBits.GuildMessages,
            GatewayIntentBits.MessageContent,
            GatewayIntentBits.DirectMessages,
            GatewayIntentBits.DirectMessageTyping,
        ],
        partials: [
            Partials.Channel,
            Partials.Message,
            Partials.User,
        ],
    })

    await client.login(TOKEN)

    return new Promise(resolve => client.on(Events.ClientReady, client => resolve(client)))
}

const client = await get_client()

console.log(`Logged in as ${client.user.tag}`)

client.on(Events.MessageCreate, async message => {
    if (message.author.bot) return

    if (message.mentions.has(client.user.id)) {
        await message.channel.send({ content: "pong!" })
    }
})
