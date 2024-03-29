import express from "express";
import cors from "cors";
import "./loadEnvironment.js";
import records from "./routes/record.js";

const PORT = process.env.PORT || 5055;
const app = express();

app.use(cors());
app.use(express.json());

app.use("/record", records);

app.listen(PORT, () => {
    console.log(`Server is running on port: ${PORT}`);
});
