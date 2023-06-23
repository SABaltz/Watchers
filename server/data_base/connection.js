import { MongoClient } from "mongodb";

const connectionString = process.env.ATLAS_URI || "";

const client = new MongoClient(connectionString);

let conn;
try {
    conn = await client.connect();
    console.log("Database successfully connected")
} catch(e) {
    console.log("Turn off your vpn")
    console.error(e);
}

let db = conn.db("dentist_watch");

export default db;
